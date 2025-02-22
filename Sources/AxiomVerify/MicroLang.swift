import Foundation
import AxiomCore
import AxiomAST
import AxiomSMT

/// Imperative commands and statements in the MicroLang verification language.
public indirect enum Stmt: Equatable, CustomStringConvertible, Sendable {
    /// No-op command
    case skip

    /// Variable assignment: x := e
    case assign(variable: Symbol, value: Expr)

    /// Sequential composition: s1 ; s2 ; ... ; sn
    case seq([Stmt])

    /// Conditional branch: if (c) { s1 } else { s2 }
    case ifThenElse(condition: Expr, thenBranch: Stmt, elseBranch: Stmt)

    /// While loop with inductive invariant annotation: while (c) invariant (I) { body }
    case whileLoop(condition: Expr, invariant: Expr?, body: Stmt)

    /// Proof obligation assertion: assert(P)
    case assert(condition: Expr, message: String?)

    /// Environment assumption: assume(P)
    case assume(condition: Expr)

    /// Non-deterministic havoc: havoc(x1, x2, ...)
    case havoc([Symbol])

    /// Heap memory read: dest := Memory[base + offset]
    case load(destination: Symbol, base: Expr, offset: Expr)

    /// Heap memory write: Memory[base + offset] := value
    case store(base: Expr, offset: Expr, value: Expr)

    /// Dynamic allocation: dest := alloc(size)
    case alloc(destination: Symbol, size: Expr)

    /// Dynamic deallocation: free(pointer)
    case free(pointer: Expr)

    // MARK: - Pretty Printing

    public var description: String {
        return format(indent: 0)
    }

    public func format(indent: Int) -> String {
        let pad = String(repeating: "  ", count: indent)
        switch self {
        case .skip:
            return "\(pad)skip;"

        case let .assign(variable, value):
            return "\(pad)\(variable.name) := \(value);"

        case let .seq(stmts):
            return stmts.map { $0.format(indent: indent) }.joined(separator: "\n")

        case let .ifThenElse(c, t, e):
            return "\(pad)if (\(c)) {\n\(t.format(indent: indent + 1))\n\(pad)} else {\n\(e.format(indent: indent + 1))\n\(pad)}"

        case let .whileLoop(c, inv, body):
            var res = "\(pad)while (\(c))"
            if let inv = inv {
                res += " invariant (\(inv))"
            }
            res += " {\n\(body.format(indent: indent + 1))\n\(pad)}"
            return res

        case let .assert(c, msg):
            let msgStr = msg.map { " \"\($0)\"" } ?? ""
            return "\(pad)assert(\(c)\(msgStr));"

        case let .assume(c):
            return "\(pad)assume(\(c));"

        case let .havoc(vars):
            let varList = vars.map { $0.name }.joined(separator: ", ")
            return "\(pad)havoc(\(varList));"

        case let .load(dest, base, offset):
            return "\(pad)\(dest.name) := *(\(base) + \(offset));"

        case let .store(base, offset, val):
            return "\(pad)*(\(base) + \(offset)) := \(val);"

        case let .alloc(dest, size):
            return "\(pad)\(dest.name) := alloc(\(size));"

        case let .free(ptr):
            return "\(pad)free(\(ptr));"
        }
    }
}

/// Typed procedure contract with Hoare pre/post conditions and frame specifications.
public struct Procedure: Equatable, CustomStringConvertible, Sendable {
    public let name: Symbol
    public let parameters: [(name: Symbol, sort: Sort)]
    public let returnSort: Sort?
    public let requires: [Expr]
    public let ensures: [Expr]
    public let modifies: [Symbol]
    public let body: Stmt

    public init(
        name: Symbol,
        parameters: [(name: Symbol, sort: Sort)] = [],
        returnSort: Sort? = nil,
        requires: [Expr] = [],
        ensures: [Expr] = [],
        modifies: [Symbol] = [],
        body: Stmt
    ) {
        self.name = name
        self.parameters = parameters
        self.returnSort = returnSort
        self.requires = requires
        self.ensures = ensures
        self.modifies = modifies
        self.body = body
    }

    public static func == (lhs: Procedure, rhs: Procedure) -> Bool {
        return lhs.name == rhs.name &&
            lhs.requires == rhs.requires &&
            lhs.ensures == rhs.ensures &&
            lhs.modifies == rhs.modifies &&
            lhs.body == rhs.body
    }

    public var description: String {
        var lines: [String] = []
        let params = parameters.map { "\($0.name.name): \($0.sort)" }.joined(separator: ", ")
        let ret = returnSort.map { " -> \($0)" } ?? ""
        lines.append("procedure \(name.name)(\(params))\(ret)")

        for req in requires {
            lines.append("  requires \(req);")
        }
        for ens in ensures {
            lines.append("  ensures \(ens);")
        }
        if !modifies.isEmpty {
            lines.append("  modifies " + modifies.map { $0.name }.joined(separator: ", ") + ";")
        }

        lines.append("{\n" + body.format(indent: 1) + "\n}")
        return lines.joined(separator: "\n")
    }
}

/// MicroLang program module encapsulating global state, procedures, and memory models.
public struct Program: Sendable {
    public var globalVariables: [Symbol: Sort]
    public var procedures: [Symbol: Procedure]

    public init(
        globalVariables: [Symbol: Sort] = [:],
        procedures: [Symbol: Procedure] = [:]
    ) {
        self.globalVariables = globalVariables
        self.procedures = procedures
    }
}
