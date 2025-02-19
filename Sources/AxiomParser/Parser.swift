import Foundation
import AxiomCore
import AxiomAST

/// A parameter binding in a define-fun command.
public struct SMTLIBParam: Equatable, Sendable {
    public let name: Symbol
    public let sort: Sort

    public init(name: Symbol, sort: Sort) {
        self.name = name
        self.sort = sort
    }
}

/// SMT-LIB 2.6 Commands parsed from script input.
public enum SMTLIBCommand: Equatable, Sendable {
    case setLogic(String)
    case setOption(keyword: String, value: String)
    case setInfo(keyword: String, value: String)
    case declareSort(name: Symbol, arity: Int)
    case declareConst(name: Symbol, sort: Sort)
    case declareFun(name: Symbol, paramSorts: [Sort], returnSort: Sort)
    case defineFun(name: Symbol, params: [SMTLIBParam], returnSort: Sort, body: Expr)
    case assert(Expr)
    case checkSat
    case checkSatAssuming([Expr])
    case getModel
    case getValue([Expr])
    case getUnsatCore
    case push(Int)
    case pop(Int)
    case exit
}

public enum SMTLIBParseError: Error, CustomStringConvertible {
    case unexpectedToken(Token, expected: String)
    case unexpectedEOF
    case invalidSort(String)
    case invalidTerm(String)

    public var description: String {
        switch self {
        case let .unexpectedToken(tok, exp):
            return "Parse error at \(tok.line):\(tok.column): unexpected '\(tok.kind)', expected \(exp)"
        case .unexpectedEOF:
            return "Parse error: unexpected end of file"
        case let .invalidSort(s):
            return "Invalid sort: \(s)"
        case let .invalidTerm(t):
            return "Invalid term: \(t)"
        }
    }
}

/// Recursive descent parser for SMT-LIB 2.6 scripts, sorts, and terms.
public final class SMTLIBParser: @unchecked Sendable {
    private let tokens: [Token]
    private var pos: Int = 0
    private var declaredSymbols: [Symbol: Sort] = [:]

    public init(tokens: [Token]) {
        self.tokens = tokens
    }

    public convenience init(input: String) {
        let lexer = SMTLIBLexer(input: input)
        self.init(tokens: lexer.tokenize())
    }

    // MARK: - Top-Level Script Parsing

    public func parseCommands() throws -> [SMTLIBCommand] {
        var commands: [SMTLIBCommand] = []
        while !isAtEnd() {
            if peek().kind == .eof { break }
            if let cmd = try parseCommand() {
                commands.append(cmd)
            }
        }
        return commands
    }

    public func parseCommand() throws -> SMTLIBCommand? {
        try consume(.leftParen, expected: "'(' to start command")
        guard let nameTok = try? consumeSymbol() else {
            throw SMTLIBParseError.unexpectedToken(peek(), expected: "command name")
        }

        let cmd: SMTLIBCommand
        switch nameTok {
        case "set-logic":
            let logic = try consumeSymbol()
            cmd = .setLogic(logic)

        case "set-option":
            let kw = try consumeKeyword()
            let val = try consumeSymbolOrNumber()
            cmd = .setOption(keyword: kw, value: val)

        case "set-info":
            let kw = try consumeKeyword()
            let val = try consumeSymbolOrString()
            cmd = .setInfo(keyword: kw, value: val)

        case "declare-sort":
            let name = Symbol(try consumeSymbol())
            let arity = try consumeInt()
            cmd = .declareSort(name: name, arity: Int(arity.magnitude.first ?? 0))

        case "declare-const":
            let name = Symbol(try consumeSymbol())
            let sort = try parseSort()
            declaredSymbols[name] = sort
            cmd = .declareConst(name: name, sort: sort)

        case "declare-fun":
            let name = Symbol(try consumeSymbol())
            try consume(.leftParen, expected: "'(' for argument sorts")
            var paramSorts: [Sort] = []
            while !check(.rightParen) {
                paramSorts.append(try parseSort())
            }
            try consume(.rightParen, expected: "')' closing argument sorts")
            let returnSort = try parseSort()
            declaredSymbols[name] = paramSorts.isEmpty ? returnSort : .function(domain: paramSorts, codomain: returnSort)
            cmd = .declareFun(name: name, paramSorts: paramSorts, returnSort: returnSort)

        case "assert":
            let term = try parseTerm()
            cmd = .assert(term)

        case "check-sat":
            cmd = .checkSat

        case "check-sat-assuming":
            try consume(.leftParen, expected: "'(' for assumption list")
            var assumptions: [Expr] = []
            while !check(.rightParen) {
                assumptions.append(try parseTerm())
            }
            try consume(.rightParen, expected: "')' closing assumptions")
            cmd = .checkSatAssuming(assumptions)

        case "get-model":
            cmd = .getModel

        case "get-unsat-core":
            cmd = .getUnsatCore

        case "get-value":
            try consume(.leftParen, expected: "'(' for get-value terms")
            var terms: [Expr] = []
            while !check(.rightParen) {
                terms.append(try parseTerm())
            }
            try consume(.rightParen, expected: "')' closing get-value")
            cmd = .getValue(terms)

        case "push":
            let count = (try? consumeInt()) ?? BigInt.one
            cmd = .push(Int(count.magnitude.first ?? 1))

        case "pop":
            let count = (try? consumeInt()) ?? BigInt.one
            cmd = .pop(Int(count.magnitude.first ?? 1))

        case "exit":
            cmd = .exit

        default:
            // Skip unknown command arguments until matching right paren
            var depth = 1
            while depth > 0 && !isAtEnd() {
                let t = advance()
                if t.kind == .leftParen { depth += 1 }
                else if t.kind == .rightParen { depth -= 1 }
            }
            return nil
        }

        try consume(.rightParen, expected: "')' to terminate command")
        return cmd
    }

    // MARK: - Sort Parsing

    public func parseSort() throws -> Sort {
        if check(.leftParen) {
            advance()
            let head = try consumeSymbol()

            if head == "_" {
                let id = try consumeSymbol()
                if id == "BitVec" {
                    let width = try consumeInt()
                    try consume(.rightParen, expected: "')' closing BitVec")
                    return .bitVec(width: Int(width.magnitude.first ?? 32))
                }
            } else if head == "Array" {
                let idxSort = try parseSort()
                let elemSort = try parseSort()
                try consume(.rightParen, expected: "')' closing Array sort")
                return .array(index: idxSort, element: elemSort)
            }

            throw SMTLIBParseError.invalidSort(head)
        }

        let name = try consumeSymbol()
        switch name {
        case "Bool": return .bool
        case "Int": return .int
        case "Real": return .real
        default: return .uninterpreted(name: Symbol(name), arity: 0)
        }
    }

    // MARK: - Term Parsing

    public func parseTerm() throws -> Expr {
        let tok = peek()

        switch tok.kind {
        case let .intNumeral(i):
            advance()
            return .intConst(i)

        case let .decimal(d):
            advance()
            return .realConst(d)

        case let .bitVector(bv):
            advance()
            return .bvConst(bv)

        case let .stringLiteral(s):
            advance()
            return .stringConst(s)

        case let .symbol(s):
            advance()
            if s == "true" { return .boolConst(true) }
            if s == "false" { return .boolConst(false) }
            let sym = Symbol(s)
            let sort = declaredSymbols[sym] ?? .int
            return .variable(name: sym, sort: sort)

        case .leftParen:
            advance()
            let term = try parseCompoundTerm()
            try consume(.rightParen, expected: "')' closing compound term")
            return term

        default:
            throw SMTLIBParseError.unexpectedToken(tok, expected: "term expression")
        }
    }

    private func parseCompoundTerm() throws -> Expr {
        // Handle indexed operator: ((_ extract 7 0) x)
        if check(.leftParen) {
            advance()
            let us = try consumeSymbol()
            if us == "_" {
                let op = try consumeSymbol()
                if op == "extract" {
                    let high = Int((try consumeInt()).magnitude.first ?? 0)
                    let low = Int((try consumeInt()).magnitude.first ?? 0)
                    try consume(.rightParen, expected: "')' closing indexed extract")
                    let body = try parseTerm()
                    return .bvExtract(high: high, low: low, body: body)
                } else if op == "zero_extend" {
                    let count = Int((try consumeInt()).magnitude.first ?? 0)
                    try consume(.rightParen, expected: "')' closing zero_extend")
                    let body = try parseTerm()
                    return .bvZeroExtend(count: count, body: body)
                } else if op == "sign_extend" {
                    let count = Int((try consumeInt()).magnitude.first ?? 0)
                    try consume(.rightParen, expected: "')' closing sign_extend")
                    let body = try parseTerm()
                    return .bvSignExtend(count: count, body: body)
                }
            }
        }

        let op = try consumeSymbol()

        // Core connectives
        switch op {
        case "not":
            return .not(try parseTerm())
        case "and":
            return .and(try parseTermsUntilEnd())
        case "or":
            return .or(try parseTermsUntilEnd())
        case "=>":
            let lhs = try parseTerm()
            let rhs = try parseTerm()
            return .implies(lhs, rhs)
        case "xor":
            return .xor(try parseTerm(), try parseTerm())
        case "=":
            let args = try parseTermsUntilEnd()
            if args.count == 2 {
                return .eq(args[0], args[1])
            }
            var eqs: [Expr] = []
            for i in 0..<(args.count - 1) {
                eqs.append(.eq(args[i], args[i + 1]))
            }
            return .and(eqs)
        case "distinct":
            return .distinct(try parseTermsUntilEnd())
        case "ite":
            let c = try parseTerm()
            let t = try parseTerm()
            let e = try parseTerm()
            return .ite(condition: c, thenBranch: t, elseBranch: e)

        // Arithmetic
        case "+":
            return .add(try parseTermsUntilEnd())
        case "-":
            let args = try parseTermsUntilEnd()
            if args.count == 1 { return .neg(args[0]) }
            return .sub(args[0], args[1])
        case "*":
            return .mul(try parseTermsUntilEnd())
        case "/":
            return .div(try parseTerm(), try parseTerm())
        case "<=":
            return .le(try parseTerm(), try parseTerm())
        case "<":
            return .lt(try parseTerm(), try parseTerm())
        case ">=":
            return .ge(try parseTerm(), try parseTerm())
        case ">":
            return .gt(try parseTerm(), try parseTerm())

        // Bit-Vectors
        case "bvadd": return .bvAdd(try parseTerm(), try parseTerm())
        case "bvsub": return .bvSub(try parseTerm(), try parseTerm())
        case "bvmul": return .bvMul(try parseTerm(), try parseTerm())
        case "bvudiv": return .bvUDiv(try parseTerm(), try parseTerm())
        case "bvurem": return .bvURem(try parseTerm(), try parseTerm())
        case "bvsdiv": return .bvSDiv(try parseTerm(), try parseTerm())
        case "bvsrem": return .bvSRem(try parseTerm(), try parseTerm())
        case "bvand": return .bvAnd(try parseTerm(), try parseTerm())
        case "bvor": return .bvOr(try parseTerm(), try parseTerm())
        case "bvxor": return .bvXor(try parseTerm(), try parseTerm())
        case "bvnot": return .bvNot(try parseTerm())
        case "bvshl": return .bvShl(try parseTerm(), try parseTerm())
        case "bvlshr": return .bvLShr(try parseTerm(), try parseTerm())
        case "bvashr": return .bvAShr(try parseTerm(), try parseTerm())
        case "concat": return .bvConcat(try parseTerm(), try parseTerm())
        case "bvult": return .bvULt(try parseTerm(), try parseTerm())
        case "bvule": return .bvULe(try parseTerm(), try parseTerm())
        case "bvslt": return .bvSLt(try parseTerm(), try parseTerm())
        case "bvsle": return .bvSLe(try parseTerm(), try parseTerm())

        // Arrays
        case "select":
            let arr = try parseTerm()
            let idx = try parseTerm()
            return .select(array: arr, index: idx)
        case "store":
            let arr = try parseTerm()
            let idx = try parseTerm()
            let val = try parseTerm()
            return .store(array: arr, index: idx, value: val)

        // General uninterpreted function application
        default:
            let sym = Symbol(op)
            let args = try parseTermsUntilEnd()
            let retSort: Sort
            if let decl = declaredSymbols[sym], case let .function(_, codomain) = decl {
                retSort = codomain
            } else {
                retSort = declaredSymbols[sym] ?? .int
            }
            return .apply(function: sym, arguments: args, returnSort: retSort)
        }
    }

    private func parseTermsUntilEnd() throws -> [Expr] {
        var terms: [Expr] = []
        while !check(.rightParen) && !isAtEnd() {
            terms.append(try parseTerm())
        }
        return terms
    }

    // MARK: - Token Helpers

    private func isAtEnd() -> Bool {
        return pos >= tokens.count || tokens[pos].kind == .eof
    }

    private func peek() -> Token {
        if isAtEnd() { return Token(kind: .eof, line: 0, column: 0) }
        return tokens[pos]
    }

    private func check(_ kind: TokenKind) -> Bool {
        return peek().kind == kind
    }

    @discardableResult
    private func advance() -> Token {
        let t = peek()
        pos += 1
        return t
    }

    private func consume(_ kind: TokenKind, expected: String) throws {
        if check(kind) {
            advance()
            return
        }
        throw SMTLIBParseError.unexpectedToken(peek(), expected: expected)
    }

    private func consumeSymbol() throws -> String {
        if case let .symbol(s) = peek().kind {
            advance()
            return s
        }
        throw SMTLIBParseError.unexpectedToken(peek(), expected: "symbol")
    }

    private func consumeKeyword() throws -> String {
        if case let .keyword(k) = peek().kind {
            advance()
            return k
        }
        throw SMTLIBParseError.unexpectedToken(peek(), expected: "keyword")
    }

    private func consumeInt() throws -> BigInt {
        if case let .intNumeral(i) = peek().kind {
            advance()
            return i
        }
        throw SMTLIBParseError.unexpectedToken(peek(), expected: "integer numeral")
    }

    private func consumeSymbolOrNumber() throws -> String {
        let tok = peek()
        switch tok.kind {
        case let .symbol(s):
            advance()
            return s
        case let .intNumeral(i):
            advance()
            return "\(i)"
        default:
            throw SMTLIBParseError.unexpectedToken(tok, expected: "symbol or number")
        }
    }

    private func consumeSymbolOrString() throws -> String {
        let tok = peek()
        switch tok.kind {
        case let .symbol(s):
            advance()
            return s
        case let .stringLiteral(s):
            advance()
            return s
        default:
            throw SMTLIBParseError.unexpectedToken(tok, expected: "symbol or string")
        }
    }
}
