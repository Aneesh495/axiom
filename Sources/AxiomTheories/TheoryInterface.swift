import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT

/// Theory identifiers for Nelson-Oppen combination and routing.
public enum TheoryId: String, CaseIterable, Sendable {
    case euf = "QF_UF"
    case lra = "QF_LRA"
    case lia = "QF_LIA"
    case bitvector = "QF_BV"
    case arrays = "QF_AX"
}

/// Result of checking theory consistency after assertions.
public enum TheoryResult: Sendable, Equatable {
    /// The current set of asserted literals is satisfiable in this theory.
    case consistent
    /// The current set of asserted literals is unsatisfiable.
    /// Contains an unsatisfiable core (explanation) of input literals that caused the refutation.
    case conflict(explanation: [Expr])
}

/// A deduction inferred by a theory solver to be propagated to the CDCL(T) engine or peer theories.
public struct TheoryDeduction: Sendable, Equatable {
    /// The inferred literal (e.g. an equality x == y or bound x <= 5).
    public let literal: Expr
    /// The subset of asserted literals that logically implies this deduction.
    public let explanation: [Expr]

    public init(literal: Expr, explanation: [Expr]) {
        self.literal = literal
        self.explanation = explanation
    }
}

/// Unified protocol implemented by all dedicated first-order theory decision procedures.
/// Supports Nelson-Oppen equality sharing, incremental scoping, and minimal conflict explanations.
public protocol TheorySolver: AnyObject {
    /// Unique theory identifier.
    var theoryId: TheoryId { get }

    /// Push an incremental backtrack scope checkpoint.
    func pushScope()

    /// Pop the most recent backtrack scope, restoring the theory state.
    func popScope()

    /// Reset the theory solver to its initial empty state.
    func reset()

    /// Incrementally assert a literal (equality, disequality, or inequality).
    /// Returns .conflict if immediate inconsistency is detected, or .consistent otherwise.
    func assertLiteral(_ literal: Expr) -> TheoryResult

    /// Perform a full consistency check over all currently asserted literals.
    func checkConsistency() -> TheoryResult

    /// Propagate newly inferred literals or shared variable equalities.
    func propagateDeductions() -> [TheoryDeduction]

    /// Extract all terms belonging to this theory or shared at theory boundaries.
    func collectSharedTerms() -> [Expr]
}

/// An assertion record stored in the theory trail.
public struct TheoryAssertionRecord: Sendable {
    public let literal: Expr
    public let scopeLevel: Int

    public init(literal: Expr, scopeLevel: Int) {
        self.literal = literal
        self.scopeLevel = scopeLevel
    }
}

/// Trail managing incremental theory assertions and scope checkpoints.
public final class TheoryTrail: @unchecked Sendable {
    private var history: [TheoryAssertionRecord] = []
    private var scopeLimits: [Int] = []

    public init() {}

    public var currentScopeLevel: Int {
        return scopeLimits.count
    }

    public func pushScope() {
        scopeLimits.append(history.count)
    }

    public func record(assertion: Expr) {
        history.append(TheoryAssertionRecord(literal: assertion, scopeLevel: currentScopeLevel))
    }

    public func popScope() -> [TheoryAssertionRecord] {
        guard let limit = scopeLimits.popLast() else { return [] }
        var popped: [TheoryAssertionRecord] = []
        while history.count > limit {
            popped.append(history.removeLast())
        }
        return popped
    }

    public func reset() {
        history.removeAll(keepingCapacity: true)
        scopeLimits.removeAll(keepingCapacity: true)
    }

    public var allAssertions: [Expr] {
        return history.map { $0.literal }
    }
}
