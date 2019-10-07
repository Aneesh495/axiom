import Foundation
import AxiomCore

/// Formula normalization converting boolean expressions into Negation Normal Form (NNF).
/// In NNF, negations appear only directly preceding atomic propositions or theory predicates.
public struct NormalForms: Sendable {
    public init() {}

    /// Converts an arbitrary first-order boolean expression into Negation Normal Form
    public func toNNF(_ expr: Expr) -> Expr {
        switch expr {
        case .boolConst, .intConst, .realConst, .bvConst, .stringConst, .variable,
             .eq, .distinct, .apply, .lt, .le, .gt, .ge, .bvULt, .bvULe, .bvSLt, .bvSLe:
            return expr

        case let .not(inner):
            return pushNegation(inner)

        case let .and(args):
            return .and(args.map { toNNF($0) })

        case let .or(args):
            return .or(args.map { toNNF($0) })

        case let .implies(lhs, rhs):
            // A => B  equiv  not(A) or B
            return .or([toNNF(.not(lhs)), toNNF(rhs)])

        case let .xor(lhs, rhs):
            // A xor B  equiv  (A and not B) or (not A and B)
            let nnfA = toNNF(lhs)
            let nnfB = toNNF(rhs)
            let notA = pushNegation(lhs)
            let notB = pushNegation(rhs)
            return .or([.and([nnfA, notB]), .and([notA, nnfB])])

        case let .iff(lhs, rhs):
            // A <=> B  equiv  (A and B) or (not A and not B)
            let nnfA = toNNF(lhs)
            let nnfB = toNNF(rhs)
            let notA = pushNegation(lhs)
            let notB = pushNegation(rhs)
            return .or([.and([nnfA, nnfB]), .and([notA, notB])])

        case let .ite(cond, thenB, elseB):
            // ite(C, T, E) equiv (C and T) or (not C and E)
            let nnfC = toNNF(cond)
            let notC = pushNegation(cond)
            return .or([.and([nnfC, toNNF(thenB)]), .and([notC, toNNF(elseB)])])

        case let .forall(vars, body):
            return .forall(variables: vars, body: toNNF(body))

        case let .exists(vars, body):
            return .exists(variables: vars, body: toNNF(body))

        default:
            return expr
        }
    }

    private func pushNegation(_ expr: Expr) -> Expr {
        switch expr {
        case let .boolConst(b):
            return .boolConst(!b)

        case let .not(inner):
            return toNNF(inner) // Double negation elimination: not(not(A)) -> A

        case let .and(args):
            // De Morgan's Law: not(and(A1, ..., An)) -> or(not A1, ..., not An)
            return .or(args.map { pushNegation($0) })

        case let .or(args):
            // De Morgan's Law: not(or(A1, ..., An)) -> and(not A1, ..., not An)
            return .and(args.map { pushNegation($0) })

        case let .implies(lhs, rhs):
            // not(A => B) equiv A and not B
            return .and([toNNF(lhs), pushNegation(rhs)])

        case let .xor(lhs, rhs):
            // not(A xor B) equiv A <=> B
            return toNNF(.iff(lhs, rhs))

        case let .iff(lhs, rhs):
            // not(A <=> B) equiv A xor B
            return toNNF(.xor(lhs, rhs))

        case let .ite(cond, thenB, elseB):
            // not(ite(C, T, E)) equiv (C and not T) or (not C and not E)
            return .or([.and([toNNF(cond), pushNegation(thenB)]),
                        .and([pushNegation(cond), pushNegation(elseB)])])

        case let .forall(vars, body):
            // not(forall x. P) equiv exists x. not P
            return .exists(variables: vars, body: pushNegation(body))

        case let .exists(vars, body):
            // not(exists x. P) equiv forall x. not P
            return .forall(variables: vars, body: pushNegation(body))

        case .eq, .distinct, .lt, .le, .gt, .ge, .bvULt, .bvULe, .bvSLt, .bvSLe, .variable, .apply:
            // Atomic theory predicates and literals stay negated
            return .not(expr)

        default:
            return .not(expr)
        }
    }
}
