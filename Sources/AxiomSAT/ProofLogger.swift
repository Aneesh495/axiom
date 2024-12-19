import Foundation

/// DRAT (Deletion Resolution Asymmetric Tautology) proof logger for certification of UNSAT results.
public final class ProofLogger: @unchecked Sendable {
    private var proofLines: [String]
    public var isEnabled: Bool

    public init(enabled: Bool = true) {
        self.proofLines = []
        self.isEnabled = enabled
    }

    /// Log addition of an asserting learned clause
    public func logAddClause(_ literals: [Literal]) {
        guard isEnabled else { return }
        let dimacsLits = literals.map { String($0.toDimacs) }.joined(separator: " ")
        proofLines.append("\(dimacsLits) 0")
    }

    /// Log deletion of a learned clause
    public func logDeleteClause(_ literals: [Literal]) {
        guard isEnabled else { return }
        let dimacsLits = literals.map { String($0.toDimacs) }.joined(separator: " ")
        proofLines.append("d \(dimacsLits) 0")
    }

    /// Log empty clause indicating refutation
    public func logEmptyClause() {
        guard isEnabled else { return }
        proofLines.append("0")
    }

    public func exportDRATProof() -> String {
        return proofLines.joined(separator: "\n") + "\n"
    }

    public func clear() {
        proofLines.removeAll(keepingCapacity: true)
    }
}
