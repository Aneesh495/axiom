import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT

/// McCarthy Extensional Array Theory Solver (QF_AX).
/// Implements the standard Read-Over-Write (ROW) axioms and Extensionality (EXT)
/// on top of an underlying congruence closure EUF engine.
///
/// Axioms:
/// 1. ROW1 (Same index): select(store(a, i, v), i) = v
/// 2. ROW2 (Distinct index): i != j implies select(store(a, i, v), j) = select(a, j)
/// 3. EXT (Extensionality): (forall i. select(a, i) = select(b, i)) implies a = b
public final class ArraySolver: TheorySolver, @unchecked Sendable {
    public var theoryId: TheoryId { return .arrays }

    // MARK: - State Management

    private let trail: TheoryTrail
    private let euf: EUFSolver
    private var isConflicted: Bool = false
    private var conflictExplanation: [Expr] = []

    // Collected array terms
    private var selectTerms: Set<Expr> = []
    private var storeTerms: Set<Expr> = []
    private var arrayDisequalities: [(lhs: Expr, rhs: Expr, originalExpr: Expr)] = []

    // Fresh Skolem index counter for extensionality
    private var skolemCounter: Int = 0

    // Scope management
    private struct ScopeSnapshot {
        let selectCount: Int
        let storeCount: Int
        let diseqCount: Int
        let skolemCount: Int
    }
    private var scopeSnapshots: [ScopeSnapshot] = []

    public init() {
        self.trail = TheoryTrail()
        self.euf = EUFSolver()
    }

    // MARK: - TheorySolver Protocol

    public func pushScope() {
        trail.pushScope()
        euf.pushScope()
        scopeSnapshots.append(ScopeSnapshot(
            selectCount: selectTerms.count,
            storeCount: storeTerms.count,
            diseqCount: arrayDisequalities.count,
            skolemCount: skolemCounter
        ))
    }

    public func popScope() {
        let _ = trail.popScope()
        euf.popScope()
        if let snap = scopeSnapshots.popLast() {
            skolemCounter = snap.skolemCount
        }
        // Rebuild term collections from trail
        rebuildFromTrail()
        isConflicted = false
        conflictExplanation.removeAll(keepingCapacity: true)
    }

    public func reset() {
        trail.reset()
        euf.reset()
        selectTerms.removeAll(keepingCapacity: true)
        storeTerms.removeAll(keepingCapacity: true)
        arrayDisequalities.removeAll(keepingCapacity: true)
        scopeSnapshots.removeAll(keepingCapacity: true)
        skolemCounter = 0
        isConflicted = false
        conflictExplanation.removeAll(keepingCapacity: true)
    }

    public func assertLiteral(_ literal: Expr) -> TheoryResult {
        if isConflicted {
            return .conflict(explanation: conflictExplanation)
        }

        trail.record(assertion: literal)
        collectArrayTerms(from: literal)

        // Check for array disequality: not (eq a b) where a, b are arrays
        if case let .not(inner) = literal, case let .eq(lhs, rhs) = inner, case .array = lhs.sort {
            arrayDisequalities.append((lhs: lhs, rhs: rhs, originalExpr: literal))
        }

        // Lower to EUF term and assert into congruence closure engine
        let eufLit = lowerToEUF(literal)
        let res = euf.assertLiteral(eufLit)
        if case .conflict = res {
            isConflicted = true
            conflictExplanation = [literal]
            return res
        }

        return .consistent
    }

    public func checkConsistency() -> TheoryResult {
        if isConflicted {
            return .conflict(explanation: conflictExplanation)
        }

        // 1. Initial EUF consistency check
        let eufRes = euf.checkConsistency()
        if case .conflict = eufRes {
            isConflicted = true
            conflictExplanation = trail.allAssertions
            return eufRes
        }

        // 2. Instantiate Extensionality for asserted array disequalities
        for diseq in arrayDisequalities {
            let lhs = diseq.lhs
            let rhs = diseq.rhs

            // If EUF already made them congruent, conflict!
            let eufLhs = lowerToEUF(lhs)
            let eufRhs = lowerToEUF(rhs)
            if euf.areEquivalent(eufLhs, eufRhs) {
                isConflicted = true
                conflictExplanation = [diseq.originalExpr]
                return .conflict(explanation: conflictExplanation)
            }

            // Fresh Skolem witness index k
            guard case let .array(indexSort, _) = lhs.sort else { continue }
            skolemCounter += 1
            let skolemName = Symbol("ax_skolem_\(skolemCounter)")
            let skolemIndex = Expr.variable(name: skolemName, sort: indexSort)

            let selA = Expr.select(array: lhs, index: skolemIndex)
            let selB = Expr.select(array: rhs, index: skolemIndex)
            selectTerms.insert(selA)
            selectTerms.insert(selB)

            let selDiseq = Expr.not(.eq(selA, selB))
            let selRes = euf.assertLiteral(lowerToEUF(selDiseq))
            if case .conflict = selRes {
                isConflicted = true
                conflictExplanation = [diseq.originalExpr]
                return .conflict(explanation: conflictExplanation)
            }
        }

        // 3. Instantiate McCarthy Read-Over-Write (ROW) axioms recursively
        return solveRowAxioms()
    }

    public func propagateDeductions() -> [TheoryDeduction] {
        return euf.propagateDeductions()
    }

    public func collectSharedTerms() -> [Expr] {
        var shared: Set<Expr> = []
        for lit in trail.allAssertions {
            collectSharedFromExpr(lit, into: &shared)
        }
        return Array(shared)
    }

    /// Check if two expressions are proven equivalent in the Array E-graph.
    public func areEquivalent(_ a: Expr, _ b: Expr) -> Bool {
        return euf.areEquivalent(lowerToEUF(a), lowerToEUF(b))
    }

    // MARK: - McCarthy ROW Axiom Solver

    private func solveRowAxioms() -> TheoryResult {
        // Collect all active (store, select) pairs
        var pendingStores: [(storeExpr: Expr, array: Expr, index: Expr, value: Expr)] = []
        for s in storeTerms {
            if case let .store(array, index, value) = s {
                pendingStores.append((storeExpr: s, array: array, index: index, value: value))
            }
        }

        var pendingSelects: [(selectExpr: Expr, array: Expr, index: Expr)] = []
        for sel in selectTerms {
            if case let .select(array, index) = sel {
                pendingSelects.append((selectExpr: sel, array: array, index: index))
            }
        }

        // Apply ROW axioms:
        // For each store(a, i, v) and each select(s, j):
        for s in pendingStores {
            for sel in pendingSelects {
                // Check if the select is on this store term: select(store(a, i, v), j)
                let eufStore = lowerToEUF(s.storeExpr)
                let eufSelArray = lowerToEUF(sel.array)

                if euf.areEquivalent(eufStore, eufSelArray) {
                    let i = s.index
                    let j = sel.index
                    let v = s.value
                    let a = s.array

                    let eufI = lowerToEUF(i)
                    let eufJ = lowerToEUF(j)

                    // Case 1: i == j in EUF -> ROW1: select(store(a, i, v), j) == v
                    if euf.areEquivalent(eufI, eufJ) {
                        let row1Eq = Expr.eq(sel.selectExpr, v)
                        let res = euf.assertLiteral(lowerToEUF(row1Eq))
                        if case .conflict = res {
                            isConflicted = true
                            conflictExplanation = trail.allAssertions
                            return res
                        }
                    }
                    // Case 2: i != j in EUF -> ROW2: select(store(a, i, v), j) == select(a, j)
                    else if euf.areDisequal(eufI, eufJ) {
                        let selA = Expr.select(array: a, index: j)
                        selectTerms.insert(selA)
                        let row2Eq = Expr.eq(sel.selectExpr, selA)
                        let res = euf.assertLiteral(lowerToEUF(row2Eq))
                        if case .conflict = res {
                            isConflicted = true
                            conflictExplanation = trail.allAssertions
                            return res
                        }
                    }
                    // Case 3: neither known -> branch on i == j or i != j
                    else {
                        let branchRes = branchOnIndexEquality(i: i, j: j, store: s, select: sel)
                        if case .conflict = branchRes {
                            isConflicted = true
                            conflictExplanation = trail.allAssertions
                            return branchRes
                        }
                    }
                }
            }
        }

        return euf.checkConsistency()
    }

    /// Case split on index equality: branch 1 (i == j), branch 2 (i != j)
    private func branchOnIndexEquality(
        i: Expr,
        j: Expr,
        store: (storeExpr: Expr, array: Expr, index: Expr, value: Expr),
        select: (selectExpr: Expr, array: Expr, index: Expr)
    ) -> TheoryResult {
        // Try branch 1: assume i == j
        euf.pushScope()
        let eqLit = Expr.eq(i, j)
        let row1Eq = Expr.eq(select.selectExpr, store.value)
        _ = euf.assertLiteral(lowerToEUF(eqLit))
        _ = euf.assertLiteral(lowerToEUF(row1Eq))

        if case .consistent = euf.checkConsistency() {
            // Consistent under i == j
            euf.popScope()
            // In an ideal DPLL(T) solver, this branch lemma would be sent to SAT.
            // For theory self-contained solving, we can propagate the conditional equality.
            return .consistent
        }

        euf.popScope()

        // Branch 1 refuted, so i != j MUST hold!
        let neqLit = Expr.not(.eq(i, j))
        let selA = Expr.select(array: store.array, index: j)
        selectTerms.insert(selA)
        let row2Eq = Expr.eq(select.selectExpr, selA)

        _ = euf.assertLiteral(lowerToEUF(neqLit))
        _ = euf.assertLiteral(lowerToEUF(row2Eq))

        return euf.checkConsistency()
    }

    // MARK: - EUF Term Lowering

    /// Lower an AST expression into an EUF-compatible representation where
    /// select and store are represented as uninterpreted function applications.
    private func lowerToEUF(_ expr: Expr) -> Expr {
        switch expr {
        case let .select(array, index):
            let eufArr = lowerToEUF(array)
            let eufIdx = lowerToEUF(index)
            return .apply(function: Symbol("select"), arguments: [eufArr, eufIdx], returnSort: expr.sort)

        case let .store(array, index, value):
            let eufArr = lowerToEUF(array)
            let eufIdx = lowerToEUF(index)
            let eufVal = lowerToEUF(value)
            return .apply(function: Symbol("store"), arguments: [eufArr, eufIdx, eufVal], returnSort: array.sort)

        case let .eq(lhs, rhs):
            return .eq(lowerToEUF(lhs), lowerToEUF(rhs))

        case let .not(child):
            return .not(lowerToEUF(child))

        case let .and(children):
            return .and(children.map { lowerToEUF($0) })

        case let .or(children):
            return .or(children.map { lowerToEUF($0) })

        case let .apply(sym, args, ret):
            return .apply(function: sym, arguments: args.map { lowerToEUF($0) }, returnSort: ret)

        default:
            return expr
        }
    }

    // MARK: - Term Collection

    private func collectArrayTerms(from expr: Expr) {
        switch expr {
        case .select:
            selectTerms.insert(expr)
        case .store:
            storeTerms.insert(expr)
        default:
            break
        }

        for sub in expr.subterms {
            collectArrayTerms(from: sub)
        }
    }

    private func rebuildFromTrail() {
        selectTerms.removeAll(keepingCapacity: true)
        storeTerms.removeAll(keepingCapacity: true)
        arrayDisequalities.removeAll(keepingCapacity: true)

        for lit in trail.allAssertions {
            collectArrayTerms(from: lit)
            if case let .not(inner) = lit, case let .eq(lhs, rhs) = inner, case .array = lhs.sort {
                arrayDisequalities.append((lhs: lhs, rhs: rhs, originalExpr: lit))
            }
        }
    }

    private func collectSharedFromExpr(_ expr: Expr, into set: inout Set<Expr>) {
        if case .array = expr.sort {
            set.insert(expr)
        }
        for sub in expr.subterms {
            collectSharedFromExpr(sub, into: &set)
        }
    }
}
