import Foundation
import AxiomCore
import AxiomAST
import AxiomSMT

/// An annotated atomic step in a concurrent thread.
public struct ThreadStep: Sendable {
    public let stepId: Int
    public let precondition: Expr
    public let statement: Stmt
    public let postcondition: Expr

    public init(stepId: Int, precondition: Expr, statement: Stmt, postcondition: Expr) {
        self.stepId = stepId
        self.precondition = precondition
        self.statement = statement
        self.postcondition = postcondition
    }
}

/// A concurrent thread modeled as a sequence of annotated atomic transitions.
public struct ConcurrentThread: Sendable {
    public let threadId: Int
    public let steps: [ThreadStep]

    public init(threadId: Int, steps: [ThreadStep]) {
        self.threadId = threadId
        self.steps = steps
    }
}

/// Result of Owicki-Gries concurrent program safety verification.
public enum ConcurrencyResult: CustomStringConvertible, Sendable {
    /// The concurrent system is verified interference-free and safe
    case safe(proofObligationsCount: Int)

    /// An interference violation was discovered between two concurrent threads
    case interferenceViolation(
        threadA: Int,
        assertion: Expr,
        threadB: Int,
        violatingStep: Int,
        model: SMTModel
    )

    public var description: String {
        switch self {
        case let .safe(count):
            return "Concurrent System Verified Safe: \(count) interference-freedom obligations discharged"
        case let .interferenceViolation(tA, ass, tB, sB, model):
            return "Interference Violation: Thread \(tB) step \(sB) invalidates Thread \(tA) assertion '\(ass)'\n\(model)"
        }
    }
}

/// Owicki-Gries Concurrent Program Safety and Interference-Freedom Verifier.
/// Verifies multi-threaded algorithms (e.g. Peterson's mutex, lock-free protocols)
/// by checking local correctness and global non-interference across all interleavings.
public final class ConcurrencyVerifier: @unchecked Sendable {
    private let solver: SMTSolver
    private let vcgen: VCGen

    public init() {
        self.solver = SMTSolver()
        self.vcgen = VCGen()
    }

    /// Verify that all thread assertions are invariant under actions of all other concurrent threads.
    public func verifyInterferenceFreedom(
        threads: [ConcurrentThread],
        globalInvariant: Expr? = nil
    ) -> ConcurrencyResult {
        var obligationsChecked = 0

        // 1. Check local sequential correctness for each thread: { Pre } S { Post }
        for thread in threads {
            for step in thread.steps {
                obligationsChecked += 1
                let (wp, _) = vcgen.computeWP(stmt: step.statement, post: step.postcondition)
                let localCorrectness = Expr.implies(step.precondition, wp)

                if !checkValid(localCorrectness) {
                    let model = solver.getModel() ?? SMTModel()
                    return .interferenceViolation(
                        threadA: thread.threadId,
                        assertion: step.postcondition,
                        threadB: thread.threadId,
                        violatingStep: step.stepId,
                        model: model
                    )
                }
            }
        }

        // 2. Check Owicki-Gries Interference Freedom across thread pairs:
        // For every assertion A in thread i, and every transition S in thread j (j != i):
        // { A /\ Pre(S) /\ GlobalInv } S { A }
        for i in 0..<threads.count {
            for j in 0..<threads.count where i != j {
                let threadA = threads[i]
                let threadB = threads[j]

                // Assertions in thread A that must be preserved
                var assertionsToPreserve: [Expr] = []
                for stepA in threadA.steps {
                    assertionsToPreserve.append(stepA.precondition)
                    assertionsToPreserve.append(stepA.postcondition)
                }

                // Interleaving transitions in thread B
                for stepB in threadB.steps {
                    for ass in assertionsToPreserve {
                        obligationsChecked += 1
                        let (wpAss, _) = vcgen.computeWP(stmt: stepB.statement, post: ass)

                        // Interference obligation: (ass /\ Pre(stepB) /\ GlobalInv) => wpAss
                        var antecedents = [ass, stepB.precondition]
                        if let gInv = globalInvariant {
                            antecedents.append(gInv)
                        }

                        let obligation = Expr.implies(Expr.and(antecedents), wpAss)
                        if !checkValid(obligation) {
                            let model = solver.getModel() ?? SMTModel()
                            return .interferenceViolation(
                                threadA: threadA.threadId,
                                assertion: ass,
                                threadB: threadB.threadId,
                                violatingStep: stepB.stepId,
                                model: model
                            )
                        }
                    }
                }
            }
        }

        return .safe(proofObligationsCount: obligationsChecked)
    }

    /// Verify mutual exclusion: prove that two threads cannot simultaneously hold their critical assertions.
    public func verifyMutualExclusion(
        thread1Critical: Expr,
        thread2Critical: Expr,
        globalInvariant: Expr? = nil
    ) -> Bool {
        solver.reset()
        var assumptions = [thread1Critical, thread2Critical]
        if let gInv = globalInvariant {
            assumptions.append(gInv)
        }

        for a in assumptions {
            _ = solver.assert(a)
        }

        // Mutex holds if simultaneous critical occupancy is UNSAT
        let res = solver.check()
        return res == .unsat
    }

    // MARK: - Helper

    private func checkValid(_ expr: Expr) -> Bool {
        solver.reset()
        _ = solver.assert(.not(expr))
        let res = solver.check()
        return res == .unsat
    }
}
