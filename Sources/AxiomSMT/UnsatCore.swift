import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT
import AxiomTheories

/// Unsatisfiable Core result containing the minimal set of contradictory assertions.
public struct UnsatCore: CustomStringConvertible, Sendable {
    /// The subset of asserted expressions responsible for the unsatisfiability
    public let expressions: [Expr]
    /// Whether this core has been proven minimal (no proper subset is unsatisfiable)
    public let isMinimal: Bool

    public init(expressions: [Expr], isMinimal: Bool) {
        self.expressions = expressions
        self.isMinimal = isMinimal
    }

    public var description: String {
        return "(unsat-core \n" + expressions.map { "  " + $0.description }.joined(separator: "\n") + "\n)"
    }
}

/// Unsatisfiable Core Extractor implementing assumption-based conflict extraction
/// and QuickXplain / Deletion Filtering core minimization.
public final class UnsatCoreExtractor: @unchecked Sendable {
    public init() {}

    /// Extract an unsatisfiable core from a set of assertions.
    /// If minimize is true, runs iterative deletion filtering to guarantee minimality.
    public func extractUnsatCore(from assertions: [Expr], minimize: Bool = true) -> UnsatCore? {
        // First verify that the full set is indeed unsatisfiable
        let initialCore = findInitialCore(assertions: assertions)
        guard let core = initialCore else {
            return nil
        }

        if !minimize || core.count <= 1 {
            return UnsatCore(expressions: core, isMinimal: core.count <= 1)
        }

        // Run deletion filtering to prune redundant constraints
        let minimalCore = deletionFilter(core: core)
        return UnsatCore(expressions: minimalCore, isMinimal: true)
    }

    // MARK: - Initial Core Extraction

    private func findInitialCore(assertions: [Expr]) -> [Expr]? {
        let engine = makeEngine()
        var assertedSoFar: [Expr] = []

        for expr in assertions {
            assertedSoFar.append(expr)
            let res = engine.assertLiteral(expr)
            if case let .conflict(explanation) = res {
                return explanation.isEmpty ? assertedSoFar : explanation
            }
        }

        let finalRes = engine.checkConsistency()
        if case let .conflict(explanation) = finalRes {
            return explanation.isEmpty ? assertedSoFar : explanation
        }

        return nil
    }

    // MARK: - Deletion Filtering Minimization

    /// Minimizes an unsat core by testing whether each assertion is essential.
    /// A constraint is essential if removing it makes the remainder satisfiable.
    private func deletionFilter(core: [Expr]) -> [Expr] {
        var currentCore = core

        var i = 0
        while i < currentCore.count {
            // Test if currentCore without item at i is still UNSAT
            var testSubset = currentCore
            testSubset.remove(at: i)

            if isUnsatisfiable(testSubset) {
                // candidate is redundant, remove it permanently
                currentCore = testSubset
            } else {
                // candidate is essential, keep it and advance
                i += 1
            }
        }

        return currentCore
    }

    private func isUnsatisfiable(_ assertions: [Expr]) -> Bool {
        let engine = makeEngine()
        for expr in assertions {
            let res = engine.assertLiteral(expr)
            if case .conflict = res {
                return true
            }
        }
        let res = engine.checkConsistency()
        if case .conflict = res {
            return true
        }
        return false
    }

    private func makeEngine() -> NelsonOppenEngine {
        let engine = NelsonOppenEngine()
        engine.registerSolver(EUFSolver())
        engine.registerSolver(LRASolver())
        engine.registerSolver(LIASolver())
        engine.registerSolver(BVSolver())
        engine.registerSolver(ArraySolver())
        return engine
    }
}
