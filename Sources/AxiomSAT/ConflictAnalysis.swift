import Foundation
import AxiomCore

/// Result of 1-UIP conflict analysis
public struct ConflictResult: Sendable {
    public let learnedClause: [Literal]
    public let backtrackLevel: Int32
    public let lbd: UInt16
}

/// 1-UIP (First Unique Implication Point) conflict clause derivation and recursive minimization.
public final class ConflictAnalyzer: @unchecked Sendable {
    private var seen: [Bool] = []

    public init() {}

    public func initForVariables(count: Int) {
        seen = [Bool](repeating: false, count: count)
    }

    private func ensureCapacity(forVariable v: Int32) {
        let needed = Int(v) + 1
        if needed > seen.count {
            seen.append(contentsOf: repeatElement(false, count: needed - seen.count))
        }
    }

    /// Analyze a conflict clause and derive the 1-UIP asserting learned clause
    public func analyze(
        conflictingClauseIndex: Int,
        clauses: [Clause],
        trail: Trail,
        vsids: VSIDS
    ) -> ConflictResult {
        let currentLevel = trail.decisionLevel
        var learnedLits: [Literal] = [Literal.undefined] // Index 0 reserved for asserting 1-UIP literal
        var backtrackLevel: Int32 = 0
        var pathCount = 0
        var p = Literal.undefined

        var trailIdx = trail.trail.count - 1
        var currentClause = clauses[conflictingClauseIndex]

        while true {
            for lit in currentClause.literals {
                let v = lit.variable
                ensureCapacity(forVariable: v)
                let vIdx = Int(v)

                if !seen[vIdx] && trail.level(of: v) > 0 {
                    seen[vIdx] = true
                    vsids.bumpActivity(for: v)

                    if trail.level(of: v) >= currentLevel {
                        pathCount += 1
                    } else {
                        learnedLits.append(lit)
                        backtrackLevel = Swift.max(backtrackLevel, trail.level(of: v))
                    }
                }
            }

            // Find next literal on trail to resolve
            while trailIdx >= 0 {
                let candidate = trail.trail[trailIdx]
                trailIdx -= 1
                let vIdx = Int(candidate.variable)
                if seen[vIdx] {
                    p = candidate
                    break
                }
            }

            seen[Int(p.variable)] = false
            pathCount -= 1

            if pathCount <= 0 {
                // p is the First Unique Implication Point (1-UIP)!
                learnedLits[0] = ~p
                break
            }

            let reasonIdx = trail.reason(of: p.variable)
            precondition(reasonIdx >= 0 && reasonIdx < clauses.count, "Reason clause missing for variable on trail")
            currentClause = clauses[reasonIdx]
        }

        // Clean seen flags for remaining learned literals
        for lit in learnedLits {
            if lit != .undefined {
                let idx = Int(lit.variable)
                if idx < seen.count { seen[idx] = false }
            }
        }

        // Recursive clause minimization
        let minimizedLits = minimizeLearnedClause(learnedLits, trail: trail, clauses: clauses)

        // Compute Literal Block Distance (LBD)
        var levelsSeen = Set<Int32>()
        for lit in minimizedLits {
            levelsSeen.insert(trail.level(of: lit.variable))
        }
        let lbd = UInt16(Swift.max(1, levelsSeen.count))

        // Recompute backtrack level after minimization
        var finalBacktrackLevel: Int32 = 0
        for i in 1..<minimizedLits.count {
            finalBacktrackLevel = Swift.max(finalBacktrackLevel, trail.level(of: minimizedLits[i].variable))
        }

        return ConflictResult(
            learnedClause: minimizedLits,
            backtrackLevel: finalBacktrackLevel,
            lbd: lbd
        )
    }

    /// Recursively minimize the learned clause by pruning redundant literals
    private func minimizeLearnedClause(
        _ literals: [Literal],
        trail: Trail,
        clauses: [Clause]
    ) -> [Literal] {
        guard literals.count > 2 else { return literals }

        var result: [Literal] = [literals[0]] // Keep 1-UIP asserting literal

        for i in 1..<literals.count {
            let lit = literals[i]
            let reasonIdx = trail.reason(of: lit.variable)
            if reasonIdx == -1 {
                result.append(lit)
            } else {
                // Check if redundant
                if !isRedundant(lit.variable, trail: trail, clauses: clauses, depth: 0) {
                    result.append(lit)
                }
            }
        }
        return result
    }

    private func isRedundant(_ v: Int32, trail: Trail, clauses: [Clause], depth: Int) -> Bool {
        if depth > 10 { return false } // Limit recursion depth
        let reasonIdx = trail.reason(of: v)
        if reasonIdx == -1 { return false }

        let reasonClause = clauses[reasonIdx]
        for lit in reasonClause.literals {
            if lit.variable == v { continue }
            if trail.level(of: lit.variable) == 0 { continue }
            let idx = Int(lit.variable)
            if idx < seen.count && seen[idx] { continue }
            if !isRedundant(lit.variable, trail: trail, clauses: clauses, depth: depth + 1) {
                return false
            }
        }
        return true
    }
}
