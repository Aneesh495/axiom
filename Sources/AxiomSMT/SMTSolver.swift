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

    @discardableResult
    public func assert(_ formula: Expr) -> SMTResult {
        assertedFormulas.append(formula)
        lastResult = .unknown
        cachedModel = nil

        // If the formula is already known to be a simple theory literal, assert directly
        let res = nelsonOppen.assertLiteral(formula)
        if case .conflict = res {
            lastResult = .unsat
            return .unsat
        }

        return .unknown
    }

    // MARK: - Solving Loop

    public func check(assumptions: [Expr] = []) -> SMTResult {
        // 1. Initial quick Nelson-Oppen check
        let noRes = nelsonOppen.checkConsistency()
        if case .conflict = noRes {
            lastResult = .unsat
            return .unsat
        }

        // 2. If all formulas are purely ground theory literals, Nelson-Oppen is complete
        if isPureTheoryConjunction() {
            lastResult = .sat
            synthesizeModel()
            return .sat
        }

        // 3. Full CDCL(T) Lazy Loop
        // Abstract non-boolean theory atoms into propositional literals
        var cnfClauses: [[Literal]] = []
        for formula in assertedFormulas + assumptions {
            let cnf = abstractToPropositional(formula)
            cnfClauses.append(contentsOf: cnf)
        }

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
                    // Satisfiable!
                    nelsonOppen.popScope()
                    lastResult = .sat
                    synthesizeModel()
                    return .sat
                }

                // Theory conflict detected: synthesize lazy theory lemma clause
                nelsonOppen.popScope()
                let lemmaClause = synthesizeTheoryLemma(explanation: conflictExplanation)
                satSolver.addClause(lemmaClause)
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

    private func isPureTheoryConjunction() -> Bool {
        for f in assertedFormulas {
            switch f {
            case .and, .or, .implies, .xor, .iff:
                return false
            default:
                break
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

    private func abstractToPropositional(_ expr: Expr) -> [[Literal]] {
        // If it's a pure boolean connective formula, Tseitin transform directly
        switch expr {
        case .and, .or, .not, .implies, .iff, .xor:
            let cnf = tseitin.transform(expr)
            return cnf.clauses.map { clause in
                clause.map { Literal(dimacs: $0) }
            }

        default:
            // Theory atom: map to a single boolean variable
            let v = getPropVar(for: expr)
            return [[Literal(variable: v, isNegated: false)]]
        }
    }

    private func getPropVar(for atom: Expr) -> Int32 {
        if let existing = atomToPropVar[atom] {
            return existing
        }
        let v = nextPropVar
        nextPropVar += 1
        atomToPropVar[atom] = v
        propVarToAtom[v] = atom
        return v
    }

    private func extractActiveTheoryLiterals() -> [Expr] {
        var active: [Expr] = []
        for (atom, propVar) in atomToPropVar {
            if satSolver.modelValue(for: propVar) {
                active.append(atom)
            } else {
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

            let propVar = getPropVar(for: baseAtom)
            // Theory conflict says: (l1 and l2) -> false, so clause is (~l1 or ~l2)
            lemmaLits.append(Literal(variable: propVar, isNegated: !isNeg))
        }
        return lemmaLits.isEmpty ? [Literal(variable: 0, isNegated: true), Literal(variable: 0, isNegated: false)] : lemmaLits
    }
}
