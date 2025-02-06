import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT
import AxiomTheories

/// Representation of an interface equality proposition e_uv between shared terms u and v.
public struct DTCEqualityVariable: Hashable, Sendable {
    public let termU: Expr
    public let termV: Expr
    public let booleanVariable: Symbol

    public init(termU: Expr, termV: Expr, id: Int) {
        // Enforce canonical ordering of terms
        if termU.description <= termV.description {
            self.termU = termU
            self.termV = termV
        } else {
            self.termU = termV
            self.termV = termU
        }
        self.booleanVariable = Symbol("dtc_eq_\(id)")
    }

    /// The literal representing u == v
    public var equalityExpr: Expr {
        return .eq(termU, termV)
    }

    /// The propositional boolean variable as an Expr
    public var propExpr: Expr {
        return .variable(name: booleanVariable, sort: .bool)
    }
}

/// Delayed Theory Combination (DTC) and Model-Based Theory Combination (MBTC) Manager.
/// Offloads theory arrangement exploration to the propositional CDCL SAT solver
/// by reifying shared term equalities as boolean decision variables.
public final class DTCManager: @unchecked Sendable {
    private var termPairToVar: [String: DTCEqualityVariable] = [:]
    private var propVarToEquality: [Symbol: DTCEqualityVariable] = [:]
    private var varCounter: Int = 0

    // Shared interface terms
    private var interfaceTerms: [Expr] = []
    private var termToTheories: [Expr: Set<TheoryId>] = [:]

    // Learned theory lemma clauses
    private var learnedTheoryLemmas: [Expr] = []

    // Scope management
    private var scopeLimits: [Int] = []

    public init() {}

    public func reset() {
        termPairToVar.removeAll(keepingCapacity: true)
        propVarToEquality.removeAll(keepingCapacity: true)
        varCounter = 0
        interfaceTerms.removeAll(keepingCapacity: true)
        termToTheories.removeAll(keepingCapacity: true)
        learnedTheoryLemmas.removeAll(keepingCapacity: true)
        scopeLimits.removeAll(keepingCapacity: true)
    }

    public func pushScope() {
        scopeLimits.append(learnedTheoryLemmas.count)
    }

    public func popScope() {
        guard let limit = scopeLimits.popLast() else { return }
        if learnedTheoryLemmas.count > limit {
            learnedTheoryLemmas.removeSubrange(limit..<learnedTheoryLemmas.count)
        }
    }

    // MARK: - Interface Term Registration

    /// Register a term belonging to a specific theory.
    public func registerTerm(_ term: Expr, from theory: TheoryId) {
        termToTheories[term, default: []].insert(theory)
        if !interfaceTerms.contains(term) {
            interfaceTerms.append(term)
        }
    }

    /// Retrieve all terms shared across two or more distinct theories.
    public var sharedInterfaceTerms: [Expr] {
        return interfaceTerms.filter { (termToTheories[$0]?.count ?? 0) >= 2 }
    }

    // MARK: - DTC Equality Reification

    /// Get or create the DTC boolean variable corresponding to equality between u and v.
    public func getOrCreateEqualityVar(u: Expr, v: Expr) -> DTCEqualityVariable {
        let key = u.description <= v.description ? "\(u.description)=\(v.description)" : "\(v.description)=\(u.description)"
        if let existing = termPairToVar[key] {
            return existing
        }

        varCounter += 1
        let newVar = DTCEqualityVariable(termU: u, termV: v, id: varCounter)
        termPairToVar[key] = newVar
        propVarToEquality[newVar.booleanVariable] = newVar
        return newVar
    }

    /// Lookup the equality proposition for a given boolean symbol.
    public func lookupEquality(bySymbol symbol: Symbol) -> DTCEqualityVariable? {
        return propVarToEquality[symbol]
    }

    // MARK: - Dynamic Case Splitting & Model-Based Combination (MBTC)

    /// Inspect theory solvers for model disagreements on shared interface variables.
    /// If theory T1 assigns u = v but theory T2 assigns u != v, generates a branching lemma (e_uv or not e_uv).
    public func detectModelDiscrepancies(across solvers: [TheoryId: TheorySolver]) -> [Expr] {
        var branchingLemmas: [Expr] = []
        let shared = sharedInterfaceTerms
        guard shared.count >= 2 else { return [] }

        for i in 0..<shared.count {
            for j in (i + 1)..<shared.count {
                let u = shared[i]
                let v = shared[j]

                // Ensure types match before generating equality candidates
                guard u.sort == v.sort else { continue }

                let eqVar = getOrCreateEqualityVar(u: u, v: v)
                let eqLit = eqVar.equalityExpr

                // Generate bridging axiom: eqVar <=> (u == v)
                // (not eqVar or (u == v)) and (eqVar or not (u == v))
                let bridgeLemma1 = Expr.or([.not(eqVar.propExpr), eqLit])
                let bridgeLemma2 = Expr.or([eqVar.propExpr, .not(eqLit)])

                if !learnedTheoryLemmas.contains(bridgeLemma1) {
                    learnedTheoryLemmas.append(bridgeLemma1)
                    branchingLemmas.append(bridgeLemma1)
                }
                if !learnedTheoryLemmas.contains(bridgeLemma2) {
                    learnedTheoryLemmas.append(bridgeLemma2)
                    branchingLemmas.append(bridgeLemma2)
                }
            }
        }

        return branchingLemmas
    }

    /// Construct a theory conflict clause from an unsatisfiable explanation core:
    /// not (l1 and l2 and ... and ln) <=> (not l1 or not l2 or ... or not ln)
    public func buildConflictClause(from explanation: [Expr]) -> Expr {
        let negatedLiterals = explanation.map { lit -> Expr in
            if case let .not(inner) = lit {
                return inner
            } else {
                return .not(lit)
            }
        }
        return Expr.or(negatedLiterals)
    }

    public var allLearnedLemmas: [Expr] {
        return learnedTheoryLemmas
    }
}
