import Foundation
import AxiomCore

/// Restart policy configuration
public enum RestartStrategy: Sendable {
    case luby(baseInterval: Int)
    case glucoseAgile(fastWindow: Int, slowWindow: Int)
    case hybrid
}

/// Dual restart engine implementing mathematical Luby universal sequences
/// and Glucose agile LBD sliding-window triggers.
public final class RestartManager: @unchecked Sendable {
    public let strategy: RestartStrategy

    // Luby state
    private var lubyIndex: Int = 1
    private var nextLubyConflictLimit: Int
    private let baseLubyInterval: Int

    // Glucose Agile state
    private var fastLBDQueue: RingBuffer<Double>
    private var slowLBDQueue: RingBuffer<Double>
    private var conflictsSinceRestart: Int = 0

    public init(strategy: RestartStrategy = .hybrid) {
        self.strategy = strategy

        switch strategy {
        case let .luby(base):
            self.baseLubyInterval = base
            self.nextLubyConflictLimit = base
            self.fastLBDQueue = RingBuffer<Double>(capacity: 50)
            self.slowLBDQueue = RingBuffer<Double>(capacity: 5000)
        case let .glucoseAgile(fast, slow):
            self.baseLubyInterval = 100
            self.nextLubyConflictLimit = 100
            self.fastLBDQueue = RingBuffer<Double>(capacity: fast)
            self.slowLBDQueue = RingBuffer<Double>(capacity: slow)
        case .hybrid:
            self.baseLubyInterval = 100
            self.nextLubyConflictLimit = 100
            self.fastLBDQueue = RingBuffer<Double>(capacity: 50)
            self.slowLBDQueue = RingBuffer<Double>(capacity: 5000)
        }
    }

    /// Record a conflict and its learned clause LBD; returns true if a restart should be triggered
    public func recordConflict(lbd: UInt16) -> Bool {
        conflictsSinceRestart += 1
        let lbdVal = Double(lbd)
        fastLBDQueue.push(lbdVal)
        slowLBDQueue.push(lbdVal)

        switch strategy {
        case .luby:
            if conflictsSinceRestart >= nextLubyConflictLimit {
                advanceLuby()
                return true
            }
            return false

        case .glucoseAgile:
            if fastLBDQueue.isFull && conflictsSinceRestart > 50 {
                // Trigger agile restart if short-term LBD is higher than 80% of long-term LBD
                if fastLBDQueue.average * 0.8 > slowLBDQueue.average {
                    conflictsSinceRestart = 0
                    return true
                }
            }
            return false

        case .hybrid:
            // Combination: check agile trigger first, fallback to Luby upper bound
            if fastLBDQueue.isFull && conflictsSinceRestart > 50 {
                if fastLBDQueue.average * 0.8 > slowLBDQueue.average {
                    conflictsSinceRestart = 0
                    advanceLuby()
                    return true
                }
            }
            if conflictsSinceRestart >= nextLubyConflictLimit {
                advanceLuby()
                return true
            }
            return false
        }
    }

    private func advanceLuby() {
        lubyIndex += 1
        let mult = computeLuby(lubyIndex)
        nextLubyConflictLimit = mult * baseLubyInterval
        conflictsSinceRestart = 0
    }

    /// Exact recursive Luby universal sequence computation:
    /// 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
    public func computeLuby(_ i: Int) -> Int {
        var size = 1
        var seq = i
        while size < seq + 1 {
            size = 2 * size + 1
        }
        while size - 1 > seq {
            size = (size - 1) >> 1
            if seq > size {
                seq -= size
            }
        }
        return (size + 1) >> 1
    }

    public func reset() {
        lubyIndex = 1
        nextLubyConflictLimit = baseLubyInterval
        conflictsSinceRestart = 0
        fastLBDQueue.clear()
        slowLBDQueue.clear()
    }
}
