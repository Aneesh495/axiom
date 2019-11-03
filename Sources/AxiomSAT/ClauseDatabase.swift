import Foundation
import AxiomCore

/// Manages problem and learned clause storage, LBD-based clause reduction, and garbage collection.
public final class ClauseDatabase: @unchecked Sendable {
    public private(set) var clauses: [Clause]
    public private(set) var learnedCount: Int = 0
    private var clauseInc: Float = 1.0
    private let clauseDecay: Float = 0.999

    public init() {
        self.clauses = []
    }

    public func addClause(_ clause: Clause) -> Int {
        let idx = clauses.count
        clauses.append(clause)
        if clause.isLearned {
            learnedCount += 1
        }
        return idx
    }

    public func bumpClauseActivity(_ clause: Clause) {
        clause.activity += clauseInc
        if clause.activity > 1e20 {
            rescaleClauseActivities()
        }
    }

    public func decayClauseActivities() {
        clauseInc *= (1.0 / clauseDecay)
    }

    private func rescaleClauseActivities() {
        for c in clauses where c.isLearned {
            c.activity *= 1e-20
        }
        clauseInc *= 1e-20
    }

    /// Reduces the learned clause database by pruning low-activity, high-LBD clauses
    public func reduce(trail: Trail) -> [Int] {
        var candidates: [(index: Int, lbd: UInt16, activity: Float)] = []

        // Collect locked reason clauses currently active on the trail
        var lockedClauses = Set<Int>()
        for lit in trail.trail {
            let r = trail.reason(of: lit.variable)
            if r != -1 {
                lockedClauses.insert(r)
            }
        }

        for (idx, c) in clauses.enumerated() {
            if !c.isLearned || c.isDeleted { continue }
            // Never delete glue clauses (LBD <= 2) or binary clauses
            if c.lbd <= 2 || c.count <= 2 { continue }
            // Never delete active reason clauses
            if lockedClauses.contains(idx) { continue }

            candidates.append((index: idx, lbd: c.lbd, activity: c.activity))
        }

        // Sort candidates: worst clauses first (high LBD first, then low activity)
        candidates.sort { a, b in
            if a.lbd != b.lbd {
                return a.lbd > b.lbd
            }
            return a.activity < b.activity
        }

        let numToDelete = candidates.count / 2
        var deletedIndices: [Int] = []

        for i in 0..<numToDelete {
            let idx = candidates[i].index
            clauses[idx].isDeleted = true
            deletedIndices.append(idx)
            learnedCount -= 1
        }

        return deletedIndices
    }

    public func clear() {
        clauses.removeAll(keepingCapacity: true)
        learnedCount = 0
        clauseInc = 1.0
    }
}
