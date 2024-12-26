import Foundation
import AxiomCore
import CAxiomKernel

/// SAT solver execution result
public enum SolverResult: Sendable, Equatable {
    case sat
    case unsat
    case unknown
}

/// SAT solver performance telemetry
public struct SATStatistics: Sendable {
    public var decisions: Int = 0
    public var propagations: Int = 0
    public var conflicts: Int = 0
    public var restarts: Int = 0
    public var learnedClauses: Int = 0
    public var reducedClauses: Int = 0
}

/// Industrial Conflict-Driven Clause Learning (CDCL) SAT Solver
/// implementing 2-watched-literals with blocking literals, 1-UIP conflict analysis,
/// recursive clause minimization, VSIDS with phase saving, Glucose agile restarts,
/// and assumption-driven incremental solving.
public final class SATSolver: @unchecked Sendable {
    public private(set) var numVariables: Int = 0
    public let trail: Trail
    public let watches: WatchedList
    public let clauseDb: ClauseDatabase
    public let vsids: VSIDS
    public let conflictAnalyzer: ConflictAnalyzer
    public let restartManager: RestartManager
    public let proofLogger: ProofLogger
    public private(set) var stats: SATStatistics

    private var propHead: Int = 0
    private var isOk: Bool = true
    private var assumptions: [Literal] = []
    private var conflictAssumptions: [Literal] = []
    private var nextReduceLimit: Int = 2000

    public init(restartStrategy: RestartStrategy = .hybrid) {
        self.trail = Trail()
        self.watches = WatchedList()
        self.clauseDb = ClauseDatabase()
        self.vsids = VSIDS()
        self.conflictAnalyzer = ConflictAnalyzer()
        self.restartManager = RestartManager(strategy: restartStrategy)
        self.proofLogger = ProofLogger()
        self.stats = SATStatistics()
    }

    // MARK: - Variable Allocation

    @discardableResult
    public func newVariable() -> Int32 {
        let v = Int32(numVariables)
        numVariables += 1
        trail.ensureCapacity(forVariable: v)
        vsids.ensureCapacity(forVariable: v)
        conflictAnalyzer.initForVariables(count: numVariables)
        return v
    }

    public func reserveVariables(count: Int) {
        while numVariables < count {
            newVariable()
        }
    }

    // MARK: - Clause Addition

    @discardableResult
    public func addClause(_ literals: [Literal]) -> Bool {
        guard isOk else { return false }

        // Remove duplicates and check for tautologies (x or not x)
        var cleaned: [Literal] = []
        var seenVars = [Int32: Bool]() // variable -> isPositive

        for lit in literals {
            let v = lit.variable
            reserveVariables(count: Int(v) + 1)

            if let existingPol = seenVars[v] {
                if existingPol != lit.isPositive {
                    // Tautology: x and ~x both in clause -> always true
                    return true
                }
                // Duplicate literal -> skip
                continue
            }
            seenVars[v] = lit.isPositive
            cleaned.append(lit)
        }

        if cleaned.isEmpty {
            isOk = false
            proofLogger.logEmptyClause()
            return false
        }

        if cleaned.count == 1 {
            let lit = cleaned[0]
            if trail.value(of: lit) == .false {
                isOk = false
                proofLogger.logEmptyClause()
                return false
            }
            if trail.value(of: lit) == .undef {
                trail.assign(literal: lit, reason: -1)
                if propagate() != nil {
                    isOk = false
                    proofLogger.logEmptyClause()
                    return false
                }
            }
            return true
        }

        let clause = Clause(literals: cleaned, isLearned: false)
        let cIdx = clauseDb.addClause(clause)

        // Attach 2 watchers to the first two literals in the clause
        watches.addWatch(literal: cleaned[0], watcher: Watcher(clauseIndex: cIdx, blocker: cleaned[1]))
        watches.addWatch(literal: cleaned[1], watcher: Watcher(clauseIndex: cIdx, blocker: cleaned[0]))

        return true
    }

    // MARK: - Two-Watched-Literal Boolean Constant Propagation (BCP)

    public func propagate() -> Int? {
        while propHead < trail.trail.count {
            let p = trail.trail[propHead]
            propHead += 1
            stats.propagations += 1

            let falseLit = ~p
            let currentWatchers = watches.watchers(for: falseLit)
            watches.clearWatchers(for: falseLit)

            var i = 0
            while i < currentWatchers.count {
                var w = currentWatchers[i]
                let cIdx = w.clauseIndex
                let clause = clauseDb.clauses[cIdx]

                if clause.isDeleted {
                    i += 1
                    continue
                }

                // Check blocker: if blocker is satisfied, clause is already satisfied
                if trail.value(of: w.blocker) == .true {
                    watches.addWatch(literal: falseLit, watcher: w)
                    i += 1
                    continue
                }

                // Ensure falseLit is at index 1
                if clause[0] == falseLit {
                    clause.literals.swapAt(0, 1)
                }

                let firstLit = clause[0]
                w.blocker = firstLit

                if trail.value(of: firstLit) == .true {
                    // Clause is satisfied by the other watched literal
                    watches.addWatch(literal: falseLit, watcher: w)
                    i += 1
                    continue
                }

                // Search for a new non-false literal to watch
                var foundNewWatch = false
                for k in 2..<clause.count {
                    if trail.value(of: clause[k]) != .false {
                        clause.literals.swapAt(1, k)
                        watches.addWatch(literal: clause[1], watcher: w)
                        foundNewWatch = true
                        break
                    }
                }

                if foundNewWatch {
                    i += 1
                    continue
                }

                // No replacement found; clause is unit or conflicting
                watches.addWatch(literal: falseLit, watcher: w)

                if trail.value(of: firstLit) == .false {
                    // Conflict detected!
                    // Put back remaining watchers
                    for j in (i + 1)..<currentWatchers.count {
                        watches.addWatch(literal: falseLit, watcher: currentWatchers[j])
                    }
                    return cIdx
                } else {
                    // Unit propagation: assign firstLit
                    trail.assign(literal: firstLit, reason: cIdx)
                }
                i += 1
            }
        }
        return nil
    }

    // MARK: - Main CDCL Solving Loop

    public func solve(assumptions: [Literal] = []) -> SolverResult {
        guard isOk else { return .unsat }
        self.assumptions = assumptions
        self.conflictAssumptions.removeAll(keepingCapacity: true)

        var assumptionIdx = 0

        while true {
            if let conflictClauseIdx = propagate() {
                // Conflict occurred
                stats.conflicts += 1

                if trail.decisionLevel == 0 {
                    // Conflict at root level -> UNSAT
                    proofLogger.logEmptyClause()
                    return .unsat
                }

                let conflict = conflictAnalyzer.analyze(
                    conflictingClauseIndex: conflictClauseIdx,
                    clauses: clauseDb.clauses,
                    trail: trail,
                    vsids: vsids
                )

                // Backtrack
                trail.backtrack(toLevel: conflict.backtrackLevel)
                propHead = trail.trail.count
                assumptionIdx = Swift.min(assumptionIdx, Int(conflict.backtrackLevel))

                // Decay activities
                vsids.decayActivities()
                clauseDb.decayClauseActivities()

                // Check for empty learned clause
                if conflict.learnedClause.isEmpty {
                    proofLogger.logEmptyClause()
                    return .unsat
                }

                proofLogger.logAddClause(conflict.learnedClause)

                if conflict.learnedClause.count == 1 {
                    // Learned unit clause
                    let unitLit = conflict.learnedClause[0]
                    trail.assign(literal: unitLit, reason: -1)
                } else {
                    let learned = Clause(
                        literals: conflict.learnedClause,
                        isLearned: true,
                        lbd: conflict.lbd
                    )
                    let newIdx = clauseDb.addClause(learned)
                    stats.learnedClauses += 1

                    // Watch the two highest level literals (0 is asserting 1-UIP)
                    watches.addWatch(literal: learned[0], watcher: Watcher(clauseIndex: newIdx, blocker: learned[1]))
                    watches.addWatch(literal: learned[1], watcher: Watcher(clauseIndex: newIdx, blocker: learned[0]))

                    // Assert 1-UIP literal
                    trail.assign(literal: learned[0], reason: newIdx)
                }

                // Check restart heuristic
                if restartManager.recordConflict(lbd: conflict.lbd) {
                    stats.restarts += 1
                    let targetLevel = Int32(Swift.min(assumptionIdx, assumptions.count))
                    trail.backtrack(toLevel: targetLevel)
                    propHead = trail.trail.count
                }

                // Check clause database reduction
                if stats.conflicts >= nextReduceLimit {
                    let deleted = clauseDb.reduce(trail: trail)
                    stats.reducedClauses += deleted.count
                    nextReduceLimit += 1500
                }
                continue
            }

            // No conflict: check assumptions
            if assumptionIdx < assumptions.count {
                let p = assumptions[assumptionIdx]
                assumptionIdx += 1

                let val = trail.value(of: p)
                if val == .true {
                    // Already satisfied at lower level
                    continue
                }
                if val == .false {
                    // Incompatible assumption -> UNSAT under assumptions
                    conflictAssumptions.append(p)
                    return .unsat
                }

                trail.newDecisionLevel()
                trail.assign(literal: p, reason: -1)
                stats.decisions += 1
                continue
            }

            // Pick decision variable using VSIDS
            guard let nextVar = vsids.selectDecisionVariable(trail: trail) else {
                // All variables assigned with no conflicts -> SAT!
                return .sat
            }

            // Phase saving: use previously cached polarity
            let polarity = trail.savedPolarity[Int(nextVar)]
            let decisionLit = Literal(variable: nextVar, isNegated: !polarity)

            trail.newDecisionLevel()
            trail.assign(literal: decisionLit, reason: -1)
            stats.decisions += 1
        }
    }

    // MARK: - Model Inspection

    public func modelValue(for variable: Int32) -> Bool {
        return trail.value(of: variable) == .true
    }

    public func modelValues() -> [Int32: Bool] {
        var model = [Int32: Bool]()
        for v in 0..<Int32(numVariables) {
            model[v] = (trail.value(of: v) == .true)
        }
        return model
    }
}
