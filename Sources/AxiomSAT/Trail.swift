import Foundation
import AxiomCore

/// Three-valued boolean logic for SAT variables
public enum LBool: Int8, Sendable {
    case `true` = 1
    case `false` = -1
    case `undef` = 0

    @inline(__always)
    public var isDefined: Bool {
        return self != .undef
    }

    @inline(__always)
    public static prefix func ! (val: LBool) -> LBool {
        switch val {
        case .true: return .false
        case .false: return .true
        case .undef: return .undef
        }
    }
}

/// Chronological assignment trail with decision level demarcation and reason tracking.
public final class Trail: @unchecked Sendable {
    /// Three-valued assignments indexed by variable index
    public private(set) var assigns: [LBool]

    /// Decision level for each variable
    public private(set) var varLevel: [Int32]

    /// Reason clause index for propagated variables (-1 for decisions)
    public private(set) var varReason: [Int]

    /// Chronological list of assigned literals
    public private(set) var trail: [Literal]

    /// Start indices in trail for each decision level
    public private(set) var trailLim: [Int]

    /// Saved polarities for phase-saving heuristic
    public private(set) var savedPolarity: [Bool]

    public init() {
        self.assigns = []
        self.varLevel = []
        self.varReason = []
        self.trail = []
        self.trailLim = []
        self.savedPolarity = []
    }

    public func initForVariables(count: Int) {
        assigns = [LBool](repeating: .undef, count: count)
        varLevel = [Int32](repeating: -1, count: count)
        varReason = [Int](repeating: -1, count: count)
        savedPolarity = [Bool](repeating: false, count: count)
        trail.removeAll(keepingCapacity: true)
        trailLim.removeAll(keepingCapacity: true)
    }

    public func ensureCapacity(forVariable v: Int32) {
        let needed = Int(v) + 1
        if needed > assigns.count {
            let addCount = needed - assigns.count
            assigns.append(contentsOf: repeatElement(.undef, count: addCount))
            varLevel.append(contentsOf: repeatElement(-1, count: addCount))
            varReason.append(contentsOf: repeatElement(-1, count: addCount))
            savedPolarity.append(contentsOf: repeatElement(false, count: addCount))
        }
    }

    // MARK: - Decision Level

    public var decisionLevel: Int32 {
        return Int32(trailLim.count)
    }

    public func newDecisionLevel() {
        trailLim.append(trail.count)
    }

    // MARK: - Query Values

    @inline(__always)
    public func value(of variable: Int32) -> LBool {
        let idx = Int(variable)
        guard idx < assigns.count else { return .undef }
        return assigns[idx]
    }

    @inline(__always)
    public func value(of literal: Literal) -> LBool {
        let val = value(of: literal.variable)
        if val == .undef { return .undef }
        return literal.isPositive ? val : !val
    }

    @inline(__always)
    public func level(of variable: Int32) -> Int32 {
        let idx = Int(variable)
        guard idx < varLevel.count else { return -1 }
        return varLevel[idx]
    }

    @inline(__always)
    public func reason(of variable: Int32) -> Int {
        let idx = Int(variable)
        guard idx < varReason.count else { return -1 }
        return varReason[idx]
    }

    // MARK: - Assignment

    public func assign(literal: Literal, reason: Int = -1) {
        let v = literal.variable
        ensureCapacity(forVariable: v)
        let idx = Int(v)

        let assignedValue: LBool = literal.isPositive ? .true : .false
        assigns[idx] = assignedValue
        varLevel[idx] = decisionLevel
        varReason[idx] = reason
        savedPolarity[idx] = literal.isPositive
        trail.append(literal)
    }

    // MARK: - Non-Chronological Backtracking

    @discardableResult
    public func backtrack(toLevel targetLevel: Int32) -> [Int32] {
        guard targetLevel < decisionLevel else { return [] }

        var unassigned: [Int32] = []
        let targetIndex = trailLim[Int(targetLevel)]
        while trail.count > targetIndex {
            let lit = trail.removeLast()
            let idx = Int(lit.variable)
            assigns[idx] = .undef
            varLevel[idx] = -1
            varReason[idx] = -1
            unassigned.append(lit.variable)
        }
        trailLim.removeSubrange(Int(targetLevel)...)
        return unassigned
    }
}
