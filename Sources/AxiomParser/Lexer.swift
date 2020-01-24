import Foundation
import AxiomCore
import AxiomAST

/// Lexical tokens for SMT-LIB 2.6 syntax.
public enum TokenKind: Equatable, CustomStringConvertible, Sendable {
    case leftParen
    case rightParen
    case symbol(String)
    case keyword(String)
    case intNumeral(BigInt)
    case decimal(Rational)
    case bitVector(BitVector)
    case stringLiteral(String)
    case eof

    public var description: String {
        switch self {
        case .leftParen: return "("
        case .rightParen: return ")"
        case let .symbol(s): return "symbol(\(s))"
        case let .keyword(k): return ":\(k)"
        case let .intNumeral(i): return "int(\(i))"
        case let .decimal(d): return "decimal(\(d))"
        case let .bitVector(bv): return "bv(\(bv))"
        case let .stringLiteral(s): return "\"\(s)\""
        case .eof: return "<eof>"
        }
    }
}

/// Token structure with source location metadata for precise diagnostics.
public struct Token: Equatable, Sendable {
    public let kind: TokenKind
    public let line: Int
    public let column: Int

    public init(kind: TokenKind, line: Int, column: Int) {
        self.kind = kind
        self.line = line
        self.column = column
    }
}

/// High-performance SMT-LIB 2.6 Lexer.
/// Scans S-expressions, symbols, bit-vector literals, decimals, and comments.
public final class SMTLIBLexer: @unchecked Sendable {
    private let chars: [Character]
    private var index: Int = 0
    private var currentLine: Int = 1
    private var currentColumn: Int = 1

    public init(input: String) {
        self.chars = Array(input)
    }

    public func tokenize() -> [Token] {
        var tokens: [Token] = []
        while true {
            let tok = nextToken()
            tokens.append(tok)
            if tok.kind == .eof {
                break
            }
        }
        return tokens
    }

    public func nextToken() -> Token {
        skipWhitespaceAndComments()

        guard index < chars.count else {
            return Token(kind: .eof, line: currentLine, column: currentColumn)
        }

        let startLine = currentLine
        let startCol = currentColumn
        let ch = chars[index]

        if ch == "(" {
            advance()
            return Token(kind: .leftParen, line: startLine, column: startCol)
        }

        if ch == ")" {
            advance()
            return Token(kind: .rightParen, line: startLine, column: startCol)
        }

        if ch == ":" {
            advance()
            let kw = scanSymbolChars()
            return Token(kind: .keyword(kw), line: startLine, column: startCol)
        }

        if ch == "\"" {
            return scanStringLiteral(startLine: startLine, startCol: startCol)
        }

        if ch == "#" {
            return scanBitVector(startLine: startLine, startCol: startCol)
        }

        if ch.isNumber {
            return scanNumber(startLine: startLine, startCol: startCol)
        }

        let sym = scanSymbolChars()
        return Token(kind: .symbol(sym), line: startLine, column: startCol)
    }

    // MARK: - Scanners

    private func scanNumber(startLine: Int, startCol: Int) -> Token {
        var numStr = ""
        while index < chars.count && (chars[index].isNumber) {
            numStr.append(chars[index])
            advance()
        }

        if index < chars.count && chars[index] == "." {
            numStr.append(".")
            advance()
            while index < chars.count && chars[index].isNumber {
                numStr.append(chars[index])
                advance()
            }
            if let rat = Rational(numStr) {
                return Token(kind: .decimal(rat), line: startLine, column: startCol)
            }
        }

        let big = BigInt(numStr) ?? BigInt.zero
        return Token(kind: .intNumeral(big), line: startLine, column: startCol)
    }

    private func scanBitVector(startLine: Int, startCol: Int) -> Token {
        advance() // skip '#'
        guard index < chars.count else {
            return Token(kind: .symbol("#"), line: startLine, column: startCol)
        }

        let kindChar = chars[index]
        advance()

        var valStr = ""
        while index < chars.count && (chars[index].isLetter || chars[index].isNumber) {
            valStr.append(chars[index])
            advance()
        }

        if kindChar == "b" {
            if let bv = BitVector(binaryString: "#b" + valStr) {
                return Token(kind: .bitVector(bv), line: startLine, column: startCol)
            }
        } else if kindChar == "x" {
            if let bv = BitVector(hexString: "#x" + valStr) {
                return Token(kind: .bitVector(bv), line: startLine, column: startCol)
            }
        }

        return Token(kind: .symbol("#" + String(kindChar) + valStr), line: startLine, column: startCol)
    }

    private func scanStringLiteral(startLine: Int, startCol: Int) -> Token {
        advance() // skip initial '"'
        var str = ""
        while index < chars.count {
            let ch = chars[index]
            if ch == "\"" {
                advance()
                if index < chars.count && chars[index] == "\"" {
                    // Escaped quote: ""
                    str.append("\"")
                    advance()
                } else {
                    break
                }
            } else {
                str.append(ch)
                advance()
            }
        }
        return Token(kind: .stringLiteral(str), line: startLine, column: startCol)
    }

    private func scanSymbolChars() -> String {
        var str = ""
        while index < chars.count {
            let ch = chars[index]
            if ch.isWhitespace || ch == "(" || ch == ")" || ch == ";" || ch == "\"" {
                break
            }
            str.append(ch)
            advance()
        }
        return str
    }

    private func skipWhitespaceAndComments() {
        while index < chars.count {
            let ch = chars[index]
            if ch == ";" {
                // SMT-LIB line comment: skip until newline
                while index < chars.count && chars[index] != "\n" {
                    advance()
                }
            } else if ch.isWhitespace {
                advance()
            } else {
                break
            }
        }
    }

    private func advance() {
        guard index < chars.count else { return }
        if chars[index] == "\n" {
            currentLine += 1
            currentColumn = 1
        } else {
            currentColumn += 1
        }
        index += 1
    }
}
