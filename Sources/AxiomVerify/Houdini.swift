import Foundation
import AxiomCore
import AxiomAST
import AxiomSMT

/// Houdini Inductive Loop Invariant Synthesizer.
/// Automatically synthesizes inductive invariants from candidate predicate pools
/// using fixed-point refutation filtering (Flanagan & Leino).
public final class HoudiniSynthesizer: @unchecked Sendable {
    private let vcgen: VCGen
    private let solver: SMTSolver

    public init() {
        self.vcgen = VCGen()
        self.solver = SMTSolver()
    }

    /// Synthesize an inductive loop invariant from a candidate pool.
    public func synthesize(
        precondition: Expr,
        loopCondition: Expr,
        loopBody: Stmt,
        candidatePool: [Expr]
    ) -> Expr? {
        var currentCandidates = candidatePool

        var changed = true
        while changed {
            changed = false
            let currentInvariant = currentCandidates.isEmpty ? Expr.boolConst(true) : Expr.and(currentCandidates)

            var survivingCandidates: [Expr] = []
            for candidate in currentCandidates {
                // 1. Check Base Case: Precondition => candidate
                if !checkImplication(lhs: precondition, rhs: candidate) {
                    changed = true
                    continue
                }

                // 2. Check Inductive Step: (currentInvariant /\ loopCondition) => wp(loopBody, candidate)
                let (wpCandidate, sideObs) = vcgen.computeWP(stmt: loopBody, post: candidate)
                let indLhs = Expr.and([currentInvariant, loopCondition])

                if !checkImplication(lhs: indLhs, rhs: wpCandidate) {
                    changed = true
                    continue
                }

                var sideObsValid = true
                for ob in sideObs {
                    if !checkImplication(lhs: indLhs, rhs: ob) {
                        sideObsValid = false
                        break
                    }
                }

                if !sideObsValid {
                    changed = true
                    continue
                }

                survivingCandidates.append(candidate)
            }

            currentCandidates = survivingCandidates
        }

        if currentCandidates.isEmpty {
            return nil
        }

        return currentCandidates.count == 1 ? currentCandidates[0] : Expr.and(currentCandidates)
    }

    // MARK: - Standard Candidate Predicate Generation

    /// Automatically generate candidate invariant predicates for integer variables.
    public func generateCandidates(variables: [Symbol], constants: [BigInt] = [0, 1]) -> [Expr] {
        var candidates: [Expr] = []

        for v in variables {
            let vExpr = Expr.variable(name: v, sort: .int)

            // Non-negativity and bounds against constants: v >= c, v <= c, v > c, v == c
            for c in constants {
                let cExpr = Expr.intConst(c)
                candidates.append(Expr.ge(vExpr, cExpr))
                candidates.append(Expr.le(vExpr, cExpr))
                candidates.append(Expr.eq(vExpr, cExpr))
            }
        }

        // Relational ordering between pairs of variables: v1 <= v2, v1 < v2, v1 == v2
        for i in 0..<variables.count {
            for j in (i + 1)..<variables.count {
                let v1 = Expr.variable(name: variables[i], sort: .int)
                let v2 = Expr.variable(name: variables[j], sort: .int)
                candidates.append(Expr.le(v1, v2))
                candidates.append(Expr.ge(v1, v2))
                candidates.append(Expr.eq(v1, v2))
            }
        }

        return candidates
    }

    // MARK: - SMT Implication Verification

    /// Checks if lhs => rhs is valid (i.e. lhs /\ not(rhs) is UNSAT).
    private func checkImplication(lhs: Expr, rhs: Expr) -> Bool {
        solver.reset()
        // Refutation: assert lhs /\ not(rhs)
        _ = solver.assert(lhs)
        _ = solver.assert(.not(rhs))

        let res = solver.check()
        return res == .unsat
    }
}
