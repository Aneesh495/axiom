import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT
import AxiomTheories

/// Result of Nelson-Oppen combined theory consistency check.
public enum NelsonOppenResult: Sendable, Equatable {
    case consistent
    case conflict(explanation: [Expr])
}

/// Purifier for mixed-theory First-Order Logic formulas.
/// Replaces alien subterms with fresh proxy variables so that every resulting
/// literal belongs to exactly one theory signature.
public final class Purifier: @unchecked Sendable {
    private var proxyCounter: Int = 0
    private var subtermToProxy: [Expr: Expr] = [:]
    private var proxyDefinitions: [(proxy: Expr, definition: Expr)] = []

    public init() {}

    public func reset() {
        proxyCounter = 0
        subtermToProxy.removeAll(keepingCapacity: true)
        proxyDefinitions.removeAll(keepingCapacity: true)
    }

    /// Purify a top-level constraint literal into pure theory literals and definitions.
    public func purify(literal: Expr) -> (purified: Expr, definitions: [Expr]) {
        let (purifiedExpr, _) = purifyTerm(literal, parentTheory: determineTheory(literal))
        let defEqualities = proxyDefinitions.map { Expr.eq($0.proxy, $0.definition) }
        return (purifiedExpr, defEqualities)
    }

    /// Recursively purify an expression, replacing alien subterms.
    private func purifyTerm(_ expr: Expr, parentTheory: TheoryId?) -> (Expr, TheoryId?) {
        let currentTheory = determineTheory(expr)

        // If this is an alien subterm under a different theory, replace with a fresh proxy variable
        if let parent = parentTheory, let current = currentTheory, parent != current, !isVariableOrConstant(expr) {
            if let existingProxy = subtermToProxy[expr] {
                return (existingProxy, parent)
            }
            proxyCounter += 1
            let proxyName = Symbol("pur_proxy_\(proxyCounter)")
            let proxyVar = Expr.variable(name: proxyName, sort: expr.sort)
            subtermToProxy[expr] = proxyVar

            // Purify the subterm definition recursively
            let (purifiedDef, _) = purifyTerm(expr, parentTheory: current)
            proxyDefinitions.append((proxy: proxyVar, definition: purifiedDef))
            return (proxyVar, parent)
        }

        // Reconstruct expression with purified subterms
        let effectiveTheory = currentTheory ?? parentTheory
        switch expr {
        case let .not(child):
            let (pChild, _) = purifyTerm(child, parentTheory: effectiveTheory)
            return (.not(pChild), effectiveTheory)

        case let .and(children):
            let pChildren = children.map { purifyTerm($0, parentTheory: effectiveTheory).0 }
            return (.and(pChildren), effectiveTheory)

        case let .or(children):
            let pChildren = children.map { purifyTerm($0, parentTheory: effectiveTheory).0 }
            return (.or(pChildren), effectiveTheory)

        case let .eq(lhs, rhs):
            let (pLhs, _) = purifyTerm(lhs, parentTheory: effectiveTheory)
            let (pRhs, _) = purifyTerm(rhs, parentTheory: effectiveTheory)
            return (.eq(pLhs, pRhs), effectiveTheory)

        case let .apply(symbol, args, retSort):
            let pArgs = args.map { purifyTerm($0, parentTheory: .euf).0 }
            return (.apply(function: symbol, arguments: pArgs, returnSort: retSort), .euf)

        case let .add(args):
            let pArgs = args.map { purifyTerm($0, parentTheory: effectiveTheory).0 }
            return (.add(pArgs), effectiveTheory)

        case let .sub(lhs, rhs):
            let (pL, _) = purifyTerm(lhs, parentTheory: effectiveTheory)
            let (pR, _) = purifyTerm(rhs, parentTheory: effectiveTheory)
            return (.sub(pL, pR), effectiveTheory)

        case let .mul(args):
            let pArgs = args.map { purifyTerm($0, parentTheory: effectiveTheory).0 }
            return (.mul(pArgs), effectiveTheory)

        case let .le(lhs, rhs):
            let (pL, _) = purifyTerm(lhs, parentTheory: effectiveTheory)
            let (pR, _) = purifyTerm(rhs, parentTheory: effectiveTheory)
            return (.le(pL, pR), effectiveTheory)

        case let .lt(lhs, rhs):
            let (pL, _) = purifyTerm(lhs, parentTheory: effectiveTheory)
            let (pR, _) = purifyTerm(rhs, parentTheory: effectiveTheory)
            return (.lt(pL, pR), effectiveTheory)

        case let .ge(lhs, rhs):
            let (pL, _) = purifyTerm(lhs, parentTheory: effectiveTheory)
            let (pR, _) = purifyTerm(rhs, parentTheory: effectiveTheory)
            return (.ge(pL, pR), effectiveTheory)

        case let .gt(lhs, rhs):
            let (pL, _) = purifyTerm(lhs, parentTheory: effectiveTheory)
            let (pR, _) = purifyTerm(rhs, parentTheory: effectiveTheory)
            return (.gt(pL, pR), effectiveTheory)

        case let .bvAdd(lhs, rhs):
            let (pL, _) = purifyTerm(lhs, parentTheory: .bitvector)
            let (pR, _) = purifyTerm(rhs, parentTheory: .bitvector)
            return (.bvAdd(pL, pR), .bitvector)

        case let .select(array, index):
            let (pArr, _) = purifyTerm(array, parentTheory: .arrays)
            let (pIdx, _) = purifyTerm(index, parentTheory: .arrays)
            return (.select(array: pArr, index: pIdx), .arrays)

        case let .store(array, index, value):
            let (pArr, _) = purifyTerm(array, parentTheory: .arrays)
            let (pIdx, _) = purifyTerm(index, parentTheory: .arrays)
            let (pVal, _) = purifyTerm(value, parentTheory: .arrays)
            return (.store(array: pArr, index: pIdx, value: pVal), .arrays)

        default:
            return (expr, effectiveTheory)
        }
    }

    private func isVariableOrConstant(_ expr: Expr) -> Bool {
        switch expr {
        case .boolConst, .intConst, .realConst, .bvConst, .stringConst, .variable:
            return true
        default:
            return false
        }
    }

    public func determineTheories(_ expr: Expr) -> [TheoryId] {
        switch expr {
        case .apply:
            return [.euf]
        case .add, .sub, .mul, .div, .mod, .neg:
            return expr.sort.isReal ? [.lra] : [.lia]
        case let .le(lhs, _), let .lt(lhs, _), let .ge(lhs, _), let .gt(lhs, _):
            return lhs.sort.isReal ? [.lra] : [.lia]
        case .bvAdd, .bvSub, .bvMul, .bvUDiv, .bvSDiv, .bvURem, .bvSRem,
             .bvAnd, .bvOr, .bvXor, .bvNot, .bvShl, .bvLShr, .bvAShr,
             .bvConcat, .bvExtract, .bvSignExtend, .bvZeroExtend,
             .bvULt, .bvULe, .bvSLt, .bvSLe:
            return [.bitvector]
        case .select, .store, .constArray:
            return [.arrays]
        case let .eq(lhs, _):
            var tids: [TheoryId] = [.euf]
            if lhs.sort.isInteger { tids.append(.lia) }
            else if lhs.sort.isReal { tids.append(.lra) }
            else if lhs.sort.isBitVector { tids.append(.bitvector) }
            else if lhs.sort.isArray { tids.append(.arrays) }
            return tids
        case let .not(child):
            return determineTheories(child)
        default:
            return [.euf]
        }
    }

    public func determineTheory(_ expr: Expr) -> TheoryId? {
        return determineTheories(expr).first
    }
}

/// Nelson-Oppen Equality Sharing Coordinating Engine.
/// Combines independent theory decision procedures by exchanging deduced equalities
/// over purified interface variables until reaching a mutual fixed point or conflict.
public final class NelsonOppenEngine: @unchecked Sendable {
    private var solvers: [TheoryId: TheorySolver]
    private let purifier: Purifier
    private var assertedLiterals: [Expr]
    private var sharedVariables: Set<Expr>
    private var deducedEqualities: Set<Expr>

    public init() {
        self.solvers = [:]
        self.purifier = Purifier()
        self.assertedLiterals = []
        self.sharedVariables = []
        self.deducedEqualities = []
    }

    public func registerSolver(_ solver: TheorySolver) {
        solvers[solver.theoryId] = solver
    }

    public func getSolver(_ id: TheoryId) -> TheorySolver? {
        return solvers[id]
    }

    public func pushScope() {
        for solver in solvers.values {
            solver.pushScope()
        }
    }

    public func popScope() {
        for solver in solvers.values {
            solver.popScope()
        }
        deducedEqualities.removeAll(keepingCapacity: true)
    }

    public func reset() {
        for solver in solvers.values {
            solver.reset()
        }
        purifier.reset()
        assertedLiterals.removeAll(keepingCapacity: true)
        sharedVariables.removeAll(keepingCapacity: true)
        deducedEqualities.removeAll(keepingCapacity: true)
    }

    /// Assert a literal across the appropriate purified theory solvers.
    public func assertLiteral(_ literal: Expr) -> NelsonOppenResult {
        assertedLiterals.append(literal)

        let (purifiedLit, defs) = purifier.purify(literal: literal)
        let allLiteralsToAssert = [purifiedLit] + defs

        for lit in allLiteralsToAssert {
            let tids = purifier.determineTheories(lit)
            for tid in tids {
                guard let solver = solvers[tid] else { continue }
                let res = solver.assertLiteral(lit)
                if case let .conflict(explanation) = res {
                    return .conflict(explanation: explanation)
                }
            }
        }

        updateSharedVariables()
        return .consistent
    }

    /// Execute the Nelson-Oppen equality sharing fixed-point loop.
    public func checkConsistency() -> NelsonOppenResult {
        // Initial individual theory consistency checks
        for (_, solver) in solvers {
            let res = solver.checkConsistency()
            if case let .conflict(explanation) = res {
                return .conflict(explanation: explanation)
            }
        }

        updateSharedVariables()
        if sharedVariables.count < 2 {
            return .consistent
        }

        // Fixed-point equality propagation loop
        var changed = true
        while changed {
            changed = false

            for (tid, solver) in solvers {
                let deductions = solver.propagateDeductions()
                for deduction in deductions {
                    if !deducedEqualities.contains(deduction.literal) {
                        deducedEqualities.insert(deduction.literal)
                        changed = true

                        // In Nelson-Oppen equality sharing, only broadcast equalities over shared interface terms
                        if case let .eq(lhs, rhs) = deduction.literal {
                            guard sharedVariables.contains(lhs) && sharedVariables.contains(rhs) else {
                                continue
                            }
                        }

                        // Broadcast to peer theory solvers that support this sort
                        let targetTheories = purifier.determineTheories(deduction.literal)
                        for targetTid in targetTheories where targetTid != tid {
                            guard let peerSolver = solvers[targetTid] else { continue }
                            let res = peerSolver.assertLiteral(deduction.literal)
                            if case let .conflict(explanation) = res {
                                let filtered = explanation.filter { $0 != deduction.literal }
                                return .conflict(explanation: filtered + deduction.explanation)
                            }
                        }
                    }
                }
            }

            // Run consistency checks after propagation step
            for (_, solver) in solvers {
                let res = solver.checkConsistency()
                if case let .conflict(explanation) = res {
                    return .conflict(explanation: explanation)
                }
            }
        }

        return .consistent
    }

    private func updateSharedVariables() {
        var varToTheories: [Expr: Set<TheoryId>] = [:]
        for (tid, solver) in solvers {
            for term in solver.collectSharedTerms() {
                if case .variable = term {
                    varToTheories[term, default: []].insert(tid)
                }
            }
        }

        sharedVariables.removeAll(keepingCapacity: true)
        for (variable, tids) in varToTheories {
            if tids.count >= 2 {
                sharedVariables.insert(variable)
            }
        }
    }
}
