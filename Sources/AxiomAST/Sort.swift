import Foundation
import AxiomCore

/// SMT-LIB 2.6 Sort (Type) system supporting primitive sorts, parameterized theories,
/// uninterpreted sorts, and function signatures.
public indirect enum Sort: Hashable, Comparable, CustomStringConvertible, Sendable {
    /// Boolean truth value sort
    case bool

    /// Unbounded mathematical integer sort
    case int

    /// Real continuous number sort
    case real

    /// Fixed-size bit-vector of width w >= 1
    case bitVec(width: Int)

    /// McCarthy extensional array sort: Array(Index, Element)
    case array(index: Sort, element: Sort)

    /// Heterogeneous tuple sort
    case tuple([Sort])

    /// Uninterpreted sort declared by the user with name and arity
    case uninterpreted(name: Symbol, arity: Int)

    /// Function signature: domain -> codomain
    case function(domain: [Sort], codomain: Sort)

    // MARK: - Properties

    public var isBoolean: Bool {
        if case .bool = self { return true }
        return false
    }

    public var isInteger: Bool {
        if case .int = self { return true }
        return false
    }

    public var isReal: Bool {
        if case .real = self { return true }
        return false
    }

    public var isArithmetic: Bool {
        return isInteger || isReal
    }

    public var isBitVector: Bool {
        if case .bitVec = self { return true }
        return false
    }

    public var bitVectorWidth: Int? {
        if case let .bitVec(w) = self { return w }
        return nil
    }

    public var isArray: Bool {
        if case .array = self { return true }
        return false
    }

    // MARK: - String Formatting

    public var description: String {
        switch self {
        case .bool:
            return "Bool"
        case .int:
            return "Int"
        case .real:
            return "Real"
        case let .bitVec(w):
            return "(_ BitVec \(w))"
        case let .array(idx, elem):
            return "(Array \(idx.description) \(elem.description))"
        case let .tuple(elements):
            let elems = elements.map(\.description).joined(separator: " ")
            return "(Tuple \(elems))"
        case let .uninterpreted(name, arity):
            return arity == 0 ? name.name : "(\(name.name) arity=\(arity))"
        case let .function(domain, codomain):
            let dom = domain.map(\.description).joined(separator: " ")
            return "(\(dom) -> \(codomain.description))"
        }
    }

    // MARK: - Comparable

    public static func < (lhs: Sort, rhs: Sort) -> Bool {
        return lhs.description < rhs.description
    }
}
