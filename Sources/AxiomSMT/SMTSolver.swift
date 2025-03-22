import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT
import AxiomTheories

/// SMT Solver execution result.
public enum SMTResult: String, CustomStringConvertible, Sendable, Equatable {
    case sat = "sat"
    case unsat = "unsat"
    case unknown = "unknown"

    public var description: String {
        return rawValue
    }
}

/// Top-level CDCL(T) Lazy Coordinating SMT Solver.
/// Integrates the industrial CDCL propositional engine with modular First-Order
/// theory solvers (EUF, LRA, LIA, BV, AX) via Tseitin abstraction, lazy lemma
/// instantiation, Nelson-Oppen equality sharing, and dynamic case splitting.
public final class SMTSolver: @unchecked Sendable {
    // Propositional CDCL core
    private var satSolver: SATSolver
    private var tseitin: TseitinTransformer
    private let dtc: DTCManager
    private let nelsonOppen: NelsonOppenEngine
    private let modelGenerator: ModelGenerator
    private let unsatCoreExtractor: UnsatCoreExtractor

    // Individual theory solvers
    public let eufSolver: EUFSolver
    public let lraSolver: LRASolver
    public let liaSolver: LIASolver
    public let bvSolver: BVSolver
    public let arraySolver: ArraySolver

    // Asserted formulas and theory atom mappings
    private var assertedFormulas: [Expr]
    private var atomToPropVar: [Expr: Int32]
    private var propVarToAtom: [Int32: Expr]
    private var nextPropVar: Int32

    // Cached results
    private var lastResult: SMTResult = .unknown
    private var cachedModel: SMTModel?

    // Incremental scope checkpoints
    private struct ScopeState {
        let formulaCount: Int
        let atomCount: Int
    }
    private var scopeStack: [ScopeState] = []

    public init() {
        self.satSolver = SATSolver()
        self.tseitin = TseitinTransformer()
        self.dtc = DTCManager()
        self.nelsonOppen = NelsonOppenEngine()
        self.modelGenerator = ModelGenerator()
        self.unsatCoreExtractor = UnsatCoreExtractor()

        self.eufSolver = EUFSolver()
        self.lraSolver = LRASolver()
        self.liaSolver = LIASolver()
        self.bvSolver = BVSolver()
        self.arraySolver = ArraySolver()

        self.assertedFormulas = []
        self.atomToPropVar = [:]
        self.propVarToAtom = [:]
        self.nextPropVar = 1

        // Register theory solvers into Nelson-Oppen engine
        nelsonOppen.registerSolver(eufSolver)
        nelsonOppen.registerSolver(lraSolver)
        nelsonOppen.registerSolver(liaSolver)
        nelsonOppen.registerSolver(bvSolver)
        nelsonOppen.registerSolver(arraySolver)
    }

    // MARK: - Incremental Scoping API

    public func push() {
        scopeStack.append(ScopeState(
            formulaCount: assertedFormulas.count,
            atomCount: atomToPropVar.count
        ))
        nelsonOppen.pushScope()
        dtc.pushScope()
    }

    public func pop() {
        guard let snap = scopeStack.popLast() else { return }
        if assertedFormulas.count > snap.formulaCount {
            assertedFormulas.removeSubrange(snap.formulaCount..<assertedFormulas.count)
        }
        nelsonOppen.popScope()
        dtc.popScope()
        lastResult = .unknown
        cachedModel = nil
    }

    public func reset() {
        satSolver = SATSolver()
        tseitin = TseitinTransformer()
        dtc.reset()
        nelsonOppen.reset()
        assertedFormulas.removeAll(keepingCapacity: true)
        atomToPropVar.removeAll(keepingCapacity: true)
        propVarToAtom.removeAll(keepingCapacity: true)
        nextPropVar = 1
        scopeStack.removeAll(keepingCapacity: true)
        lastResult = .unknown
        cachedModel = nil
    }

    // MARK: - Assertion

    private func flattenConjunctions(_ formulas: [Expr]) -> [Expr] {
        var flat: [Expr] = []
        for f in formulas {
            if case let .and(children) = f {
                flat.append(contentsOf: flattenConjunctions(children))
            } else {
                flat.append(f)
            }
        }
        return flat
    }

    @discardableResult
    public func assert(_ formula: Expr) -> SMTResult {
        if case let .and(conjuncts) = formula {
            for c in conjuncts {
                _ = self.assert(c)
            }
            return .unknown
        }
        assertedFormulas.append(formula)
        lastResult = .unknown
        cachedModel = nil
        return .unknown
    }

    // MARK: - Solving Loop

    public func check(assumptions: [Expr] = []) -> SMTResult {
        let allFormulas = flattenConjunctions(assertedFormulas + assumptions)
        guard !allFormulas.isEmpty else {
            lastResult = .sat
            synthesizeModel()
            return .sat
        }

        if allFormulas.contains(.boolConst(false)) {
            lastResult = .unsat
            return .unsat
        }

        // 1. If all formulas are purely ground theory literals, Nelson-Oppen is complete
        if isPureTheoryConjunction(formulas: allFormulas) {
            nelsonOppen.pushScope()
            for f in allFormulas {
                let res = nelsonOppen.assertLiteral(f)
                if case .conflict = res {
                    nelsonOppen.popScope()
                    lastResult = .unsat
                    return .unsat
                }
            }

            let noRes = nelsonOppen.checkConsistency()
            if case .conflict = noRes {
                nelsonOppen.popScope()
                lastResult = .unsat
                return .unsat
            }

            lastResult = .sat
            synthesizeModel()
            nelsonOppen.popScope()
            return .sat
        }

        // 2. Full CDCL(T) Lazy Loop
        let cnfClauses = setupPropositionalAbstraction(formulas: allFormulas)
        satSolver = SATSolver()
        for clause in cnfClauses {
            satSolver.addClause(clause)
        }

        // CDCL(T) Search Loop
        while true {
            let satRes = satSolver.solve()
            switch satRes {
            case .unsat:
                lastResult = .unsat
                return .unsat

            case .unknown:
                lastResult = .unknown
                return .unknown

            case .sat:
                // Extract active theory literals from propositional model
                let activeLiterals = extractActiveTheoryLiterals()

                nelsonOppen.pushScope()
                var conflictOccurred = false
                var conflictExplanation: [Expr] = []

                for lit in activeLiterals {
                    let aRes = nelsonOppen.assertLiteral(lit)
                    if case let .conflict(explanation) = aRes {
                        conflictOccurred = true
                        conflictExplanation = explanation
                        break
                    }
                }

                if !conflictOccurred {
                    let cRes = nelsonOppen.checkConsistency()
                    if case let .conflict(explanation) = cRes {
                        conflictOccurred = true
                        conflictExplanation = explanation
                    }
                }

                if !conflictOccurred {
                    // Consistent with all theories: satisfiable!
                    nelsonOppen.popScope()
                    lastResult = .sat
                    synthesizeModel()
                    return .sat
                }

                // Theory conflict detected: backtrack SAT solver to root, learn lemma clause
                nelsonOppen.popScope()
                let lemmaClause = synthesizeTheoryLemma(explanation: conflictExplanation)
                satSolver.backtrackToRoot()
                if !satSolver.addClause(lemmaClause) {
                    lastResult = .unsat
                    return .unsat
                }
            }
        }
    }

    // MARK: - Model and Proof Inspection

    public func getModel() -> SMTModel? {
        if lastResult == .sat {
            if cachedModel == nil {
                synthesizeModel()
            }
            return cachedModel
        }
        return nil
    }

    public func getUnsatCore() -> UnsatCore? {
        guard lastResult == .unsat else { return nil }
        return unsatCoreExtractor.extractUnsatCore(from: assertedFormulas)
    }

    // MARK: - Helpers

    private func isTheoryAtom(_ expr: Expr) -> Bool {
        switch expr {
        case .boolConst, .and, .or, .not, .implies, .iff, .xor, .ite:
            return false
        default:
            return true
        }
    }

    private func isPureTheoryLiteral(_ expr: Expr) -> Bool {
        switch expr {
        case .eq, .distinct, .le, .lt, .ge, .gt, .bvULt, .bvULe, .bvSLt, .bvSLe, .apply:
            return true
        case let .not(inner):
            return isPureTheoryLiteral(inner)
        case let .variable(_, sort):
            return sort == .bool
        case .boolConst:
            return true
        default:
            return false
        }
    }

    private func isPureTheoryConjunction(formulas: [Expr]) -> Bool {
        for f in formulas {
            if !isPureTheoryLiteral(f) {
                return false
            }
        }
        return true
    }

    private func synthesizeModel() {
        var allVars = Set<Expr>()
        for f in assertedFormulas {
            collectVariables(f, into: &allVars)
        }

        cachedModel = modelGenerator.generateModel(
            variables: allVars,
            satSolver: satSolver,
            lraSolver: lraSolver,
            liaSolver: liaSolver,
            bvSolver: bvSolver,
            arraySolver: arraySolver
        )
    }

    private func collectVariables(_ expr: Expr, into set: inout Set<Expr>) {
        if case .variable = expr {
            set.insert(expr)
        }
        for sub in expr.subterms {
            collectVariables(sub, into: &set)
        }
    }

    private func setupPropositionalAbstraction(formulas: [Expr]) -> [[Literal]] {
        atomToPropVar.removeAll(keepingCapacity: true)
        propVarToAtom.removeAll(keepingCapacity: true)
        nextPropVar = 1

        let rootExpr: Expr
        if formulas.isEmpty {
            rootExpr = .boolConst(true)
        } else if formulas.count == 1 {
            rootExpr = formulas[0]
        } else {
            rootExpr = .and(formulas)
        }

        let cnf = tseitin.transform(rootExpr)

        for (atomExpr, varId) in cnf.exprToVar {
            if isTheoryAtom(atomExpr) {
                let satVar = varId - 1 // 0-based SAT variable index
                atomToPropVar[atomExpr] = satVar
                propVarToAtom[satVar] = atomExpr
            }
        }

        return cnf.clauses.map { clause in
            clause.map { Literal(dimacs: $0) }
        }
    }

    private func extractActiveTheoryLiterals() -> [Expr] {
        var active: [Expr] = []
        for (atom, propVar) in atomToPropVar {
            let val = satSolver.trail.value(of: propVar)
            if val == .true {
                active.append(atom)
            } else if val == .false {
                active.append(Expr.not(atom))
            }
        }
        return active
    }

    private func synthesizeTheoryLemma(explanation: [Expr]) -> [Literal] {
        var lemmaLits: [Literal] = []
        for exp in explanation {
            let isNeg: Bool
            let baseAtom: Expr
            if case let .not(inner) = exp {
                isNeg = true
                baseAtom = inner
            } else {
                isNeg = false
                baseAtom = exp
            }

            if let propVar = atomToPropVar[baseAtom] {
                lemmaLits.append(Literal(variable: propVar, isNegated: !isNeg))
            }
        }

        if lemmaLits.isEmpty {
            for (_, propVar) in atomToPropVar {
                let val = satSolver.trail.value(of: propVar)
                if val == .true {
                    lemmaLits.append(Literal(variable: propVar, isNegated: true))
                } else if val == .false {
                    lemmaLits.append(Literal(variable: propVar, isNegated: false))
                }
            }
        }

        return lemmaLits
    }
}
