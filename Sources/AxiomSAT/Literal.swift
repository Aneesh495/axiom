import Foundation

/// Highly optimized 32-bit propositional literal encoding.
/// Variable v is encoded as (v << 1) for positive literal, and (v << 1 | 1) for negative literal.
public struct Literal: Hashable, Equatable, Comparable, CustomStringConvertible, Sendable {
    public let rawValue: UInt32

    @inline(__always)
    public init(rawValue: UInt32) {
        self.rawValue = rawValue
    }

    @inline(__always)
    public init(variable: Int32, isNegated: Bool) {
        precondition(variable >= 0, "Variable index must be non-negative")
        self.rawValue = (UInt32(variable) << 1) | (isNegated ? 1 : 0)
    }

    /// Construct from standard 1-based signed DIMACS integer literal (e.g. +3 or -3)
    public init(dimacs: Int32) {
        precondition(dimacs != 0, "DIMACS literal cannot be zero")
        let varIdx = Swift.abs(dimacs) - 1
        let isNeg = dimacs < 0
        self.init(variable: varIdx, isNegated: isNeg)
    }

    public static let undefined = Literal(rawValue: UInt32.max)

    @inline(__always)
    public var variable: Int32 {
        return Int32(rawValue >> 1)
    }

    @inline(__always)
    public var isPositive: Bool {
        return (rawValue & 1) == 0
    }

    @inline(__always)
    public var isNegative: Bool {
        return (rawValue & 1) == 1
    }

    @inline(__always)
    public var negated: Literal {
        return Literal(rawValue: rawValue ^ 1)
    }

    @inline(__always)
    public static prefix func ~ (lit: Literal) -> Literal {
        return lit.negated
    }

    public var toDimacs: Int32 {
        guard variable >= 0 && variable < (Int32.max - 1) else { return 0 }
        let v = variable + 1
        return isNegative ? -v : v
    }

    public static func < (lhs: Literal, rhs: Literal) -> Bool {
        return lhs.rawValue < rhs.rawValue
    }

    public var description: String {
        return isNegative ? "¬x\(variable)" : "x\(variable)"
    }
}
