import Foundation

/// SAT clause structure maintaining literal array, LBD (Literal Block Distance), and learned status.
public final class Clause: @unchecked Sendable {
    public var literals: [Literal]
    public var isLearned: Bool
    public var lbd: UInt16
    public var activity: Float
    public var isDeleted: Bool

    public init(literals: [Literal], isLearned: Bool = false, lbd: UInt16 = 0) {
        self.literals = literals
        self.isLearned = isLearned
        self.lbd = lbd
        self.activity = 0.0
        self.isDeleted = false
    }

    public var count: Int {
        return literals.count
    }

    public var isEmpty: Bool {
        return literals.isEmpty
    }

    public subscript(index: Int) -> Literal {
        get { return literals[index] }
        set { literals[index] = newValue }
    }

    public var description: String {
        let lits = literals.map(\.description).joined(separator: " ∨ ")
        return "(\(lits))" + (isLearned ? " [LBD=\(lbd)]" : "")
    }
}
