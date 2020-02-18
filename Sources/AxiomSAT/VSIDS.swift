import Foundation
import AxiomCore

/// VSIDS (Variable State Independent Decaying Sum) decision heuristic
/// managing dynamic activity scores, exponential decay, and phase-saving polarity.
public final class VSIDS: @unchecked Sendable {
    private var orderHeap: IndexedPriorityQueue<Int32, Double>
    private var activities: [Double]
    private var varInc: Double
    private let varDecay: Double
    private let rescaleThreshold: Double = 1e100

    public init(decay: Double = 0.95) {
        self.orderHeap = IndexedPriorityQueue<Int32, Double>.maxHeap()
        self.activities = []
        self.varInc = 1.0
        self.varDecay = decay
    }

    public func initForVariables(count: Int) {
        activities = [Double](repeating: 0.0, count: count)
        orderHeap.clear()
        for v in 0..<Int32(count) {
            orderHeap.insert(element: v, priority: 0.0)
        }
    }

    public func ensureCapacity(forVariable v: Int32) {
        let needed = Int(v) + 1
        if needed > activities.count {
            let start = activities.count
            activities.append(contentsOf: repeatElement(0.0, count: needed - start))
            for i in start..<needed {
                orderHeap.insert(element: Int32(i), priority: 0.0)
            }
        }
    }

    /// Bump the activity score of a variable involved in conflict resolution
    public func bumpActivity(for variable: Int32) {
        ensureCapacity(forVariable: variable)
        let idx = Int(variable)
        activities[idx] += varInc
        if activities[idx] > rescaleThreshold {
            rescaleActivities()
        }
        orderHeap.updatePriority(element: variable, newPriority: activities[idx])
    }

    /// Decay all activity scores by scaling up the increment
    public func decayActivities() {
        varInc *= (1.0 / varDecay)
    }

    /// Re-insert an unassigned variable back into the decision priority queue
    public func insertVariable(_ v: Int32) {
        if !orderHeap.contains(v) {
            let act = Int(v) < activities.count ? activities[Int(v)] : 0.0
            orderHeap.insert(element: v, priority: act)
        }
    }

    /// Select the unassigned variable with the highest activity score
    public func selectDecisionVariable(trail: Trail) -> Int32? {
        while let top = orderHeap.pop() {
            let v = top.element
            if trail.value(of: v) == .undef {
                return v
            }
        }
        return nil
    }

    private func rescaleActivities() {
        for i in 0..<activities.count {
            activities[i] *= 1e-100
            orderHeap.updatePriority(element: Int32(i), newPriority: activities[i])
        }
        varInc *= 1e-100
    }
}
