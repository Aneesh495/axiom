import Foundation
import AxiomCore

/// Variable binding for first-order quantifiers
public struct QuantifierVar: Hashable, Sendable {
    public let name: Symbol
    public let sort: Sort

    public init(name: Symbol, sort: Sort) {
        self.name = name
        self.sort = sort
    }
}

/// First-Order Logic Abstract Syntax Tree node representing terms, predicates, and formulas.
/// Features structural hashing, sort inference, and subterm extraction for SMT-LIB 2.6.
public indirect enum Expr: Hashable, CustomStringConvertible, Sendable {
    // MARK: - Constants
    case boolConst(Bool)
    case intConst(BigInt)
    case realConst(Rational)
    case bvConst(BitVector)
    case stringConst(String)

    // MARK: - Variables
    case variable(name: Symbol, sort: Sort)

    // MARK: - Propositional Connectives
    case not(Expr)
    case and([Expr])
    case or([Expr])
    case implies(Expr, Expr)
    case xor(Expr, Expr)
    case iff(Expr, Expr)
    case ite(condition: Expr, thenBranch: Expr, elseBranch: Expr)

    // MARK: - Equality & Uninterpreted Functions
    case eq(Expr, Expr)
    case distinct([Expr])
    case apply(function: Symbol, arguments: [Expr], returnSort: Sort)

    // MARK: - Arithmetic (LRA / LIA)
    case add([Expr])
    case sub(Expr, Expr)
    case neg(Expr)
    case mul([Expr])
    case div(Expr, Expr)
    case mod(Expr, Expr)
    case lt(Expr, Expr)
    case le(Expr, Expr)
    case gt(Expr, Expr)
    case ge(Expr, Expr)

    // MARK: - Bit-Vector Theory (QF_BV)
    case bvAdd(Expr, Expr)
    case bvSub(Expr, Expr)
    case bvMul(Expr, Expr)
    case bvUDiv(Expr, Expr)
    case bvSDiv(Expr, Expr)
    case bvURem(Expr, Expr)
    case bvSRem(Expr, Expr)
    case bvAnd(Expr, Expr)
    case bvOr(Expr, Expr)
    case bvXor(Expr, Expr)
    case bvNot(Expr)
    case bvShl(Expr, Expr)
    case bvLShr(Expr, Expr)
    case bvAShr(Expr, Expr)
    case bvConcat(Expr, Expr)
    case bvExtract(high: Int, low: Int, body: Expr)
    case bvSignExtend(count: Int, body: Expr)
    case bvZeroExtend(count: Int, body: Expr)
    case bvULt(Expr, Expr)
    case bvULe(Expr, Expr)
    case bvSLt(Expr, Expr)
    case bvSLe(Expr, Expr)

    // MARK: - Array Theory (QF_AX)
    case select(array: Expr, index: Expr)
    case store(array: Expr, index: Expr, value: Expr)
    case constArray(indexSort: Sort, value: Expr)

    // MARK: - Quantifiers
    case forall(variables: [QuantifierVar], body: Expr)
    case exists(variables: [QuantifierVar], body: Expr)

    // MARK: - Convenience Constructors

    public static let `true` = Expr.boolConst(true)
    public static let `false` = Expr.boolConst(false)

    public static func int(_ value: BigInt) -> Expr {
        return .intConst(value)
    }

    public static func real(_ num: Int64, _ den: Int64 = 1) -> Expr {
        return .realConst(Rational(BigInt(num), BigInt(den)))
    }

    public static func real(_ value: Rational) -> Expr {
        return .realConst(value)
    }

    public static func bv(width: Int, value: UInt64) -> Expr {
        return .bvConst(BitVector(width: width, value: value))
    }

    public static func bv(_ bv: BitVector) -> Expr {
        return .bvConst(bv)
    }

    public static func variable(_ name: String, _ sort: Sort) -> Expr {
        return .variable(name: Symbol(name), sort: sort)
    }

    // MARK: - Sort Inference

    public var sort: Sort {
        switch self {
        case .boolConst:
            return .bool
        case .intConst:
            return .int
        case .realConst:
            return .real
        case let .bvConst(bv):
            return .bitVec(width: bv.width)
        case .stringConst:
            return .uninterpreted(name: Symbol("String"), arity: 0)

        case let .variable(_, sort):
            return sort

        case .not, .and, .or, .implies, .xor, .iff:
            return .bool
        case let .ite(_, thenBranch, _):
            return thenBranch.sort

        case .eq, .distinct:
            return .bool
        case let .apply(_, _, returnSort):
            return returnSort

        case let .add(args):
            return args.first?.sort ?? .int
        case let .sub(lhs, _):
            return lhs.sort
        case let .neg(body):
            return body.sort
        case let .mul(args):
            return args.first?.sort ?? .int
        case let .div(lhs, _):
            return lhs.sort
        case let .mod(lhs, _):
            return lhs.sort
        case .lt, .le, .gt, .ge:
            return .bool

        case let .bvAdd(lhs, _):
            return lhs.sort
        case let .bvSub(lhs, _):
            return lhs.sort
        case let .bvMul(lhs, _):
            return lhs.sort
        case let .bvUDiv(lhs, _):
            return lhs.sort
        case let .bvSDiv(lhs, _):
            return lhs.sort
        case let .bvURem(lhs, _):
            return lhs.sort
        case let .bvSRem(lhs, _):
            return lhs.sort
        case let .bvAnd(lhs, _):
            return lhs.sort
        case let .bvOr(lhs, _):
            return lhs.sort
        case let .bvXor(lhs, _):
            return lhs.sort
        case let .bvNot(body):
            return body.sort
        case let .bvShl(lhs, _):
            return lhs.sort
        case let .bvLShr(lhs, _):
            return lhs.sort
        case let .bvAShr(lhs, _):
            return lhs.sort
        case let .bvConcat(lhs, rhs):
            let wL = lhs.sort.bitVectorWidth ?? 0
            let wR = rhs.sort.bitVectorWidth ?? 0
            return .bitVec(width: wL + wR)
        case let .bvExtract(high, low, _):
            return .bitVec(width: high - low + 1)
        case let .bvSignExtend(count, body):
            let w = body.sort.bitVectorWidth ?? 0
            return .bitVec(width: w + count)
        case let .bvZeroExtend(count, body):
            let w = body.sort.bitVectorWidth ?? 0
            return .bitVec(width: w + count)
        case .bvULt, .bvULe, .bvSLt, .bvSLe:
            return .bool

        case let .select(array, _):
            if case let .array(_, elementSort) = array.sort {
                return elementSort
            }
            return .int
        case let .store(array, _, _):
            return array.sort
        case let .constArray(indexSort, value):
            return .array(index: indexSort, element: value.sort)

        case .forall, .exists:
            return .bool
        }
    }

    // MARK: - Free Variables

    public var freeVariables: Set<Symbol> {
        var vars = Set<Symbol>()
        collectFreeVariables(into: &vars)
        return vars
    }

    private func collectFreeVariables(into set: inout Set<Symbol>) {
        switch self {
        case let .variable(name, _):
            set.insert(name)
        case let .not(e), let .neg(e), let .bvNot(e), let .bvExtract(_, _, e),
             let .bvSignExtend(_, e), let .bvZeroExtend(_, e), let .constArray(_, e):
            e.collectFreeVariables(into: &set)
        case let .and(es), let .or(es), let .distinct(es), let .add(es), let .mul(es):
            for e in es { e.collectFreeVariables(into: &set) }
        case let .implies(a, b), let .xor(a, b), let .iff(a, b), let .eq(a, b),
             let .sub(a, b), let .div(a, b), let .mod(a, b), let .lt(a, b),
             let .le(a, b), let .gt(a, b), let .ge(a, b), let .bvAdd(a, b),
             let .bvSub(a, b), let .bvMul(a, b), let .bvUDiv(a, b), let .bvSDiv(a, b),
             let .bvURem(a, b), let .bvSRem(a, b), let .bvAnd(a, b), let .bvOr(a, b),
             let .bvXor(a, b), let .bvShl(a, b), let .bvLShr(a, b), let .bvAShr(a, b),
             let .bvConcat(a, b), let .bvULt(a, b), let .bvULe(a, b), let .bvSLt(a, b),
             let .bvSLe(a, b), let .select(a, b):
            a.collectFreeVariables(into: &set)
            b.collectFreeVariables(into: &set)
        case let .ite(c, t, e):
            c.collectFreeVariables(into: &set)
            t.collectFreeVariables(into: &set)
            e.collectFreeVariables(into: &set)
        case let .store(a, i, v):
            a.collectFreeVariables(into: &set)
            i.collectFreeVariables(into: &set)
            v.collectFreeVariables(into: &set)
        case let .apply(_, args, _):
            for arg in args { arg.collectFreeVariables(into: &set) }
        case let .forall(bound, body), let .exists(bound, body):
            var bodyVars = body.freeVariables
            for qv in bound {
                bodyVars.remove(qv.name)
            }
            set.formUnion(bodyVars)
        case .boolConst, .intConst, .realConst, .bvConst, .stringConst:
            break
        }
    }

    public var isGround: Bool {
        return freeVariables.isEmpty
    }

    // MARK: - Direct Subterms

    public var subterms: [Expr] {
        switch self {
        case .boolConst, .intConst, .realConst, .bvConst, .stringConst, .variable:
            return []
        case let .not(e), let .neg(e), let .bvNot(e), let .bvExtract(_, _, e),
             let .bvSignExtend(_, e), let .bvZeroExtend(_, e), let .constArray(_, e):
            return [e]
        case let .and(es), let .or(es), let .distinct(es), let .add(es), let .mul(es):
            return es
        case let .implies(a, b), let .xor(a, b), let .iff(a, b), let .eq(a, b),
             let .sub(a, b), let .div(a, b), let .mod(a, b), let .lt(a, b),
             let .le(a, b), let .gt(a, b), let .ge(a, b), let .bvAdd(a, b),
             let .bvSub(a, b), let .bvMul(a, b), let .bvUDiv(a, b), let .bvSDiv(a, b),
             let .bvURem(a, b), let .bvSRem(a, b), let .bvAnd(a, b), let .bvOr(a, b),
             let .bvXor(a, b), let .bvShl(a, b), let .bvLShr(a, b), let .bvAShr(a, b),
             let .bvConcat(a, b), let .bvULt(a, b), let .bvULe(a, b), let .bvSLt(a, b),
             let .bvSLe(a, b), let .select(a, b):
            return [a, b]
        case let .ite(c, t, e):
            return [c, t, e]
        case let .store(a, i, v):
            return [a, i, v]
        case let .apply(_, args, _):
            return args
        case let .forall(_, body), let .exists(_, body):
            return [body]
        }
    }

    // MARK: - SMT-LIB 2.6 Serialization

    public var description: String {
        switch self {
        case let .boolConst(b):
            return b ? "true" : "false"
        case let .intConst(i):
            return i.isNegative ? "(- \((-i).description))" : i.description
        case let .realConst(r):
            return r.isNegative ? "(- \((-r).description))" : r.description
        case let .bvConst(bv):
            return bv.hexDescription
        case let .stringConst(s):
            return "\"\(s)\""
        case let .variable(name, _):
            return name.name
        case let .not(e):
            return "(not \(e.description))"
        case let .and(args):
            return args.isEmpty ? "true" : "(and \(args.map(\.description).joined(separator: " ")))"
        case let .or(args):
            return args.isEmpty ? "false" : "(or \(args.map(\.description).joined(separator: " ")))"
        case let .implies(a, b):
            return "(=> \(a.description) \(b.description))"
        case let .xor(a, b):
            return "(xor \(a.description) \(b.description))"
        case let .iff(a, b):
            return "(= \(a.description) \(b.description))"
        case let .ite(c, t, e):
            return "(ite \(c.description) \(t.description) \(e.description))"
        case let .eq(a, b):
            return "(= \(a.description) \(b.description))"
        case let .distinct(args):
            return "(distinct \(args.map(\.description).joined(separator: " ")))"
        case let .apply(f, args, _):
            if args.isEmpty { return f.name }
            return "(\(f.name) \(args.map(\.description).joined(separator: " ")))"
        case let .add(args):
            return "(+ \(args.map(\.description).joined(separator: " ")))"
        case let .sub(a, b):
            return "(- \(a.description) \(b.description))"
        case let .neg(e):
            return "(- \(e.description))"
        case let .mul(args):
            return "(* \(args.map(\.description).joined(separator: " ")))"
        case let .div(a, b):
            return "(/ \(a.description) \(b.description))"
        case let .mod(a, b):
            return "(mod \(a.description) \(b.description))"
        case let .lt(a, b):
            return "(< \(a.description) \(b.description))"
        case let .le(a, b):
            return "(<= \(a.description) \(b.description))"
        case let .gt(a, b):
            return "(> \(a.description) \(b.description))"
        case let .ge(a, b):
            return "(>= \(a.description) \(b.description))"
        case let .bvAdd(a, b):
            return "(bvadd \(a.description) \(b.description))"
        case let .bvSub(a, b):
            return "(bvsub \(a.description) \(b.description))"
        case let .bvMul(a, b):
            return "(bvmul \(a.description) \(b.description))"
        case let .bvUDiv(a, b):
            return "(bvudiv \(a.description) \(b.description))"
        case let .bvSDiv(a, b):
            return "(bvsdiv \(a.description) \(b.description))"
        case let .bvURem(a, b):
            return "(bvurem \(a.description) \(b.description))"
        case let .bvSRem(a, b):
            return "(bvsrem \(a.description) \(b.description))"
        case let .bvAnd(a, b):
            return "(bvand \(a.description) \(b.description))"
        case let .bvOr(a, b):
            return "(bvor \(a.description) \(b.description))"
        case let .bvXor(a, b):
            return "(bvxor \(a.description) \(b.description))"
        case let .bvNot(e):
            return "(bvnot \(e.description))"
        case let .bvShl(a, b):
            return "(bvshl \(a.description) \(b.description))"
        case let .bvLShr(a, b):
            return "(bvlshr \(a.description) \(b.description))"
        case let .bvAShr(a, b):
            return "(bvashr \(a.description) \(b.description))"
        case let .bvConcat(a, b):
            return "(concat \(a.description) \(b.description))"
        case let .bvExtract(high, low, e):
            return "((_ extract \(high) \(low)) \(e.description))"
        case let .bvSignExtend(count, e):
            return "((_ sign_extend \(count)) \(e.description))"
        case let .bvZeroExtend(count, e):
            return "((_ zero_extend \(count)) \(e.description))"
        case let .bvULt(a, b):
            return "(bvult \(a.description) \(b.description))"
        case let .bvULe(a, b):
            return "(bvule \(a.description) \(b.description))"
        case let .bvSLt(a, b):
            return "(bvslt \(a.description) \(b.description))"
        case let .bvSLe(a, b):
            return "(bvsle \(a.description) \(b.description))"
        case let .select(arr, idx):
            return "(select \(arr.description) \(idx.description))"
        case let .store(arr, idx, val):
            return "(store \(arr.description) \(idx.description) \(val.description))"
        case let .constArray(idxSort, val):
            return "((as const \(idxSort.description)) \(val.description))"
        case let .forall(vars, body):
            let vStr = vars.map { "(\($0.name.name) \($0.sort.description))" }.joined(separator: " ")
            return "(forall (\(vStr)) \(body.description))"
        case let .exists(vars, body):
            let vStr = vars.map { "(\($0.name.name) \($0.sort.description))" }.joined(separator: " ")
            return "(exists (\(vStr)) \(body.description))"
        }
    }
}
