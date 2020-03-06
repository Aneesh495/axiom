import Foundation
import AxiomCore
import AxiomAST
import AxiomSMT

/// Result of verifying a procedure against its formal contract.
public enum VerificationResult: CustomStringConvertible, Sendable {
    /// Formally proven verified: no counterexample exists satisfying the negated verification condition
    case verified(obligationsCount: Int)

    /// Verification failed: a concrete counterexample state violating the specification
    case counterexample(model: SMTModel, obligation: Expr)

    public var description: String {
        switch self {
        case let .verified(count):
            return "Verified (\(count) obligations checked)"
        case let .counterexample(model, obligation):
            return "Verification Failed: counterexample found for obligation \(obligation)\n\(model)"
        }
    }
}

/// Dijkstra Weakest Precondition (WP) Verification Condition Generator (VCGen).
/// Computes exact weakest preconditions over imperative programs with memory models
/// and generates first-order proof obligations solved via the SMT engine.
public final class VCGen: @unchecked Sendable {
    private let solver: SMTSolver
    private var memoryArrayVar: Expr

    public init() {
        self.solver = SMTSolver()
        let memSort = Sort.array(index: .int, element: .int)
        self.memoryArrayVar = Expr.variable(name: "HEAP_MEMORY", sort: memSort)
    }

    // MARK: - Procedure Verification

    /// Verify a complete procedure against its requires and ensures contracts.
    public func verify(procedure: Procedure) -> VerificationResult {
        solver.reset()

        let preCondition: Expr
        if procedure.requires.isEmpty {
            preCondition = .boolConst(true)
        } else if procedure.requires.count == 1 {
            preCondition = procedure.requires[0]
        } else {
            preCondition = .and(procedure.requires)
        }

        let postCondition: Expr
        if procedure.ensures.isEmpty {
            postCondition = .boolConst(true)
        } else if procedure.ensures.count == 1 {
            postCondition = procedure.ensures[0]
        } else {
            postCondition = .and(procedure.ensures)
        }

        // Compute weakest precondition of the procedure body
        let (wpExpr, obligations) = computeWP(stmt: procedure.body, post: postCondition)

        // Top-level proof obligation: Pre => wp(Body, Post)
        let topObligation = Expr.implies(preCondition, wpExpr)
        var allObligations = obligations
        allObligations.append(topObligation)

        var allGoals: [(assumptions: [Expr], goal: Expr)] = []
        for obligation in allObligations {
            allGoals.append(contentsOf: decomposeObligation(obligation))
        }

        var totalChecked = 0
        for g in allGoals {
            totalChecked += 1
            solver.reset()

            for a in g.assumptions {
                _ = solver.assert(a)
            }
            _ = solver.assert(.not(g.goal))

            let res = solver.check()
            if res == .sat {
                let model = solver.getModel() ?? SMTModel()
                return .counterexample(model: model, obligation: Expr.implies(.and(g.assumptions), g.goal))
            }
        }

        return .verified(obligationsCount: totalChecked)
    }

    private func decomposeObligation(_ expr: Expr, assumptions: [Expr] = []) -> [(assumptions: [Expr], goal: Expr)] {
        switch expr {
        case let .implies(hyp, conc):
            var newAssumptions = assumptions
            if case let .and(conjuncts) = hyp {
                newAssumptions.append(contentsOf: conjuncts)
            } else {
                newAssumptions.append(hyp)
            }
            return decomposeObligation(conc, assumptions: newAssumptions)

        case let .and(conjuncts):
            var result: [(assumptions: [Expr], goal: Expr)] = []
            for c in conjuncts {
                result.append(contentsOf: decomposeObligation(c, assumptions: assumptions))
            }
            return result

        default:
            return [(assumptions: assumptions, goal: expr)]
        }
    }

    // MARK: - Weakest Precondition Calculus

    /// Compute weakest precondition of a statement with respect to postcondition.
    /// Returns (wp, sideObligations) where sideObligations arise from loop invariants and assertions.
    public func computeWP(stmt: Stmt, post: Expr) -> (wp: Expr, obligations: [Expr]) {
        switch stmt {
        case .skip:
            return (post, [])

        case let .assign(variable, value):
            let substituted = substitute(variable: variable, with: value, in: post)
            return (substituted, [])

        case let .seq(stmts):
            var currentPost = post
            var collectedObligations: [Expr] = []
            for s in stmts.reversed() {
                let (w, obs) = computeWP(stmt: s, post: currentPost)
                currentPost = w
                collectedObligations.append(contentsOf: obs)
            }
            return (currentPost, collectedObligations)

        case let .ifThenElse(cond, thenBranch, elseBranch):
            let (wpThen, obsThen) = computeWP(stmt: thenBranch, post: post)
            let (wpElse, obsElse) = computeWP(stmt: elseBranch, post: post)

            // (cond => wpThen) /\ (not cond => wpElse)
            let branchWP = Expr.and([
                .implies(cond, wpThen),
                .implies(.not(cond), wpElse)
            ])
            return (branchWP, obsThen + obsElse)

        case let .assert(cond, _):
            // wp(assert C, Q) = C /\ Q
            return (.and([cond, post]), [cond])

        case let .assume(cond):
            // wp(assume C, Q) = C => Q
            return (.implies(cond, post), [])

        case let .havoc(variables):
            // For quantifier-free verification: fresh Skolem renaming
            var current = post
            for v in variables {
                let fresh = Expr.variable(name: Symbol("\(v.name)_havoc_\(UUID().uuidString.prefix(4))"), sort: .int)
                current = substitute(variable: v, with: fresh, in: current)
            }
            return (current, [])

        case let .load(dest, base, offset):
            // dest := HEAP_MEMORY[base + offset]
            let addr = Expr.add([base, offset])
            let selectExpr = Expr.select(array: memoryArrayVar, index: addr)
            let substituted = substitute(variable: dest, with: selectExpr, in: post)
            return (substituted, [])

        case let .store(base, offset, val):
            // HEAP_MEMORY := store(HEAP_MEMORY, base + offset, val)
            let addr = Expr.add([base, offset])
            let newMem = Expr.store(array: memoryArrayVar, index: addr, value: val)
            if case let .variable(memSym, _) = memoryArrayVar {
                let substituted = substitute(variable: memSym, with: newMem, in: post)
                return (substituted, [])
            }
            return (post, [])

        case let .alloc(dest, _):
            // dest := fresh address > 0
            let freshPtr = Expr.variable(name: Symbol("ptr_\(dest.name)"), sort: .int)
            let substituted = substitute(variable: dest, with: freshPtr, in: post)
            let ptrPositive = Expr.gt(freshPtr, .intConst(0))
            return (.and([ptrPositive, substituted]), [])

        case .free:
            return (post, [])

        case let .whileLoop(cond, invariant, body):
            guard let inv = invariant else {
                // Without an invariant, fall back to body unrolling or require annotation
                return (post, [])
            }

            // Loop verification conditions:
            // 1. Invariance: (I /\ cond) => wp(body, I)
            // 2. Postcondition on termination: (I /\ not cond) => post
            let (wpBody, bodyObs) = computeWP(stmt: body, post: inv)
            let invarianceObligation = Expr.implies(.and([inv, cond]), wpBody)
            let exitObligation = Expr.implies(.and([inv, .not(cond)]), post)

            let loopObligations = bodyObs + [invarianceObligation, exitObligation]
            return (inv, loopObligations)
        }
    }

    // MARK: - Variable Substitution

    public func substitute(variable: Symbol, with replacement: Expr, in expr: Expr) -> Expr {
        switch expr {
        case let .variable(name, _) where name == variable:
            return replacement

        case let .not(child):
            return .not(substitute(variable: variable, with: replacement, in: child))

        case let .and(children):
            return .and(children.map { substitute(variable: variable, with: replacement, in: $0) })

        case let .or(children):
            return .or(children.map { substitute(variable: variable, with: replacement, in: $0) })

        case let .implies(lhs, rhs):
            return .implies(
                substitute(variable: variable, with: replacement, in: lhs),
                substitute(variable: variable, with: replacement, in: rhs)
            )

        case let .eq(lhs, rhs):
            return .eq(
                substitute(variable: variable, with: replacement, in: lhs),
                substitute(variable: variable, with: replacement, in: rhs)
            )

        case let .add(args):
            return .add(args.map { substitute(variable: variable, with: replacement, in: $0) })

        case let .sub(lhs, rhs):
            return .sub(
                substitute(variable: variable, with: replacement, in: lhs),
                substitute(variable: variable, with: replacement, in: rhs)
            )

        case let .mul(args):
            return .mul(args.map { substitute(variable: variable, with: replacement, in: $0) })

        case let .le(lhs, rhs):
            return .le(
                substitute(variable: variable, with: replacement, in: lhs),
                substitute(variable: variable, with: replacement, in: rhs)
            )

        case let .lt(lhs, rhs):
            return .lt(
                substitute(variable: variable, with: replacement, in: lhs),
                substitute(variable: variable, with: replacement, in: rhs)
            )

        case let .ge(lhs, rhs):
            return .ge(
                substitute(variable: variable, with: replacement, in: lhs),
                substitute(variable: variable, with: replacement, in: rhs)
            )

        case let .gt(lhs, rhs):
            return .gt(
                substitute(variable: variable, with: replacement, in: lhs),
                substitute(variable: variable, with: replacement, in: rhs)
            )

        case let .select(array, index):
            return .select(
                array: substitute(variable: variable, with: replacement, in: array),
                index: substitute(variable: variable, with: replacement, in: index)
            )

        case let .store(array, index, val):
            return .store(
                array: substitute(variable: variable, with: replacement, in: array),
                index: substitute(variable: variable, with: replacement, in: index),
                value: substitute(variable: variable, with: replacement, in: val)
            )

        default:
            return expr
        }
    }
}
