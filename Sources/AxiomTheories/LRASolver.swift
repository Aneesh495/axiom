import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT

/// A bound on a linear real arithmetic variable with justification expression.
public struct BoundInfo: Sendable, Equatable {
    public let value: Rational
    public let reason: Expr
    public let isStrict: Bool

    public init(value: Rational, reason: Expr, isStrict: Bool = false) {
        self.value = value
        self.reason = reason
        self.isStrict = isStrict
    }
}

/// A linear term represented as a linear combination of variables with exact rational coefficients.
public struct LinearPolynomial: Sendable {
    public var terms: [Int: Rational] // variableId -> coefficient
    public var constant: Rational

    public init(terms: [Int: Rational] = [:], constant: Rational = .zero) {
        self.terms = terms
        self.constant = constant
    }

    public mutating func addTerm(variable: Int, coefficient: Rational) {
        let newCoeff = (terms[variable] ?? .zero) + coefficient
        if newCoeff.isZero {
            terms.removeValue(forKey: variable)
        } else {
            terms[variable] = newCoeff
        }
    }
}

/// Incremental Dual Simplex tableau solver for Quantifier-Free Linear Real Arithmetic (QF_LRA).
/// Implements the Dutertre-de Moura algorithm with exact rational arithmetic.
public final class LRASolver: TheorySolver, @unchecked Sendable {
    public let theoryId: TheoryId = .lra

    // Variable management
    public private(set) var varCount: Int = 0
    private var exprToVar: [Expr: Int] = [:]
    private var varToExpr: [Int: Expr] = [:]

    // Tableau representation: basicVar -> (nonBasicVar -> coefficient)
    // Invariant: basicVar = sum(a_ij * x_j)
    private var tableau: [Int: [Int: Rational]] = [:]
    private var basicVars: Set<Int> = []
    private var nonBasicVars: Set<Int> = []

    // Bounds and assignments
    private var lowerBounds: [Int: BoundInfo] = [:]
    private var upperBounds: [Int: BoundInfo] = [:]
    private var values: [Int: Rational] = [:]

    // Backtracking undo history
    private struct BoundUndo: Sendable {
        let variable: Int
        let oldLower: BoundInfo?
        let oldUpper: BoundInfo?
    }

    private var undoHistory: [BoundUndo] = []
    private var scopeLimits: [Int] = []

    // Asserted input constraints
    private var assertedConstraints: [Expr] = []
    private var pendingDeductions: [TheoryDeduction] = []

    private var isConflicted: Bool = false
    private var conflictExplanation: [Expr] = []
    private var conflictScopeLevel: Int? = nil

    public init() {}

    // MARK: - Variable & Term Allocation

    /// Register an expression as an LRA variable.
    public func registerVariable(_ expr: Expr) -> Int {
        if let existing = exprToVar[expr] {
            return existing
        }
        let v = varCount
        varCount += 1
        exprToVar[expr] = v
        varToExpr[v] = expr
        nonBasicVars.insert(v)
        values[v] = .zero
        return v
    }

    // MARK: - Tableau Construction & Pivoting

    /// Add a constraint as a new row in the tableau: basicVar = sum(coeff * nonBasicVar)
    public func addRow(basicVar: Int, terms: [Int: Rational]) {
        var substitutedTerms: [Int: Rational] = [:]

        for (v, coeff) in terms {
            if basicVars.contains(v) {
                // v is currently a basic variable: substitute its definition
                if let vRow = tableau[v] {
                    for (nbVar, nbCoeff) in vRow {
                        let newCoeff = (substitutedTerms[nbVar] ?? .zero) + coeff * nbCoeff
                        if newCoeff.isZero {
                            substitutedTerms.removeValue(forKey: nbVar)
                        } else {
                            substitutedTerms[nbVar] = newCoeff
                        }
                    }
                }
            } else {
                // v is non-basic
                let newCoeff = (substitutedTerms[v] ?? .zero) + coeff
                if newCoeff.isZero {
                    substitutedTerms.removeValue(forKey: v)
                } else {
                    substitutedTerms[v] = newCoeff
                }
            }
        }

        tableau[basicVar] = substitutedTerms
        basicVars.insert(basicVar)
        nonBasicVars.remove(basicVar)
        values[basicVar] = computeRowValue(basicVar)
    }

    private func computeRowValue(_ basicVar: Int) -> Rational {
        guard let row = tableau[basicVar] else { return .zero }
        var sum = Rational.zero
        for (nbVar, coeff) in row {
            sum = sum + coeff * (values[nbVar] ?? .zero)
        }
        return sum
    }

    /// Perform a standard Gauss-Jordan tableau pivot swapping basicVar and nonBasicVar.
    public func pivot(basic: Int, nonBasic: Int) {
        guard var pivotRow = tableau[basic], let a_ij = pivotRow[nonBasic], !a_ij.isZero else {
            return
        }

        // 1. Solve pivot row for nonBasic:
        // x_i = a_ij * x_j + sum_{k != j} a_ik * x_k
        // <=> x_j = (1 / a_ij) * x_i - sum_{k != j} (a_ik / a_ij) * x_k
        pivotRow.removeValue(forKey: nonBasic)
        let invA = Rational(1) / a_ij

        var newNonBasicRow: [Int: Rational] = [:]
        newNonBasicRow[basic] = invA
        for (k, coeff) in pivotRow {
            newNonBasicRow[k] = -coeff * invA
        }

        tableau.removeValue(forKey: basic)
        tableau[nonBasic] = newNonBasicRow

        // 2. Substitute new expression into all other rows
        for (otherBasic, otherRow) in tableau where otherBasic != nonBasic {
            if let a_kj = otherRow[nonBasic], !a_kj.isZero {
                var updatedRow = otherRow
                updatedRow.removeValue(forKey: nonBasic)
                for (k, coeff) in newNonBasicRow {
                    let existing = updatedRow[k] ?? .zero
                    let newCoeff = existing + a_kj * coeff
                    if newCoeff.isZero {
                        updatedRow.removeValue(forKey: k)
                    } else {
                        updatedRow[k] = newCoeff
                    }
                }
                tableau[otherBasic] = updatedRow
            }
        }

        // 3. Update variable partition
        basicVars.remove(basic)
        nonBasicVars.insert(basic)
        basicVars.insert(nonBasic)
        nonBasicVars.remove(nonBasic)
    }

    // MARK: - Dual Simplex Feasibility Check

    /// Run Dual Simplex to restore feasibility across all basic variable bounds.
    public func checkFeasibility() -> TheoryResult {
        if isConflicted {
            return .conflict(explanation: conflictExplanation)
        }

        let maxIterations = 5000
        var iteration = 0

        while iteration < maxIterations {
            iteration += 1

            // Find a basic variable that violates its bounds
            guard let violatingBasic = findViolatingBasicVar() else {
                // All basic variables satisfy their bounds: tableau is feasible!
                return .consistent
            }

            let val = values[violatingBasic] ?? .zero
            let isLowerViolation = lowerBounds[violatingBasic] != nil && val < lowerBounds[violatingBasic]!.value

            // Find candidate non-basic variable to pivot with
            guard let pivotCol = findPivotColumn(basicVar: violatingBasic, isLowerViolation: isLowerViolation) else {
                // No column can repair the violation: unsatisfiable conflict!
                let explanation = buildFarkasConflict(violatingBasic: violatingBasic, isLowerViolation: isLowerViolation)
                isConflicted = true
                conflictExplanation = explanation
                conflictScopeLevel = scopeLimits.count
                return .conflict(explanation: explanation)
            }

            // Update value of nonBasic to repair violatingBasic
            let targetVal = isLowerViolation
                ? lowerBounds[violatingBasic]!.value
                : upperBounds[violatingBasic]!.value
            let delta = targetVal - val
            let a_ij = tableau[violatingBasic]![pivotCol]!
            let theta = delta / a_ij

            values[violatingBasic] = targetVal
            values[pivotCol] = (values[pivotCol] ?? .zero) + theta
            pivot(basic: violatingBasic, nonBasic: pivotCol)

            // Recompute values for all basic variables
            for bVar in basicVars {
                values[bVar] = computeRowValue(bVar)
            }
        }

        return .consistent
    }

    /// Select basic variable violating bounds using Bland's rule (smallest variable index).
    private func findViolatingBasicVar() -> Int? {
        var candidates: [Int] = []
        for bVar in basicVars {
            let val = values[bVar] ?? .zero
            if let lb = lowerBounds[bVar], val < lb.value {
                candidates.append(bVar)
            } else if let ub = upperBounds[bVar], val > ub.value {
                candidates.append(bVar)
            }
        }
        return candidates.min()
    }

    /// Select non-basic variable to pivot using Bland's rule.
    private func findPivotColumn(basicVar: Int, isLowerViolation: Bool) -> Int? {
        guard let row = tableau[basicVar] else { return nil }
        var validCandidates: [Int] = []

        for (nbVar, coeff) in row {
            let nbVal = values[nbVar] ?? .zero
            if isLowerViolation {
                // Need to increase basicVar
                // coeff > 0: can increase nbVar if nbVal < upperBound
                if coeff > .zero {
                    if upperBounds[nbVar] == nil || nbVal < upperBounds[nbVar]!.value {
                        validCandidates.append(nbVar)
                    }
                } else if coeff < .zero {
                    // coeff < 0: can decrease nbVar if nbVal > lowerBound
                    if lowerBounds[nbVar] == nil || nbVal > lowerBounds[nbVar]!.value {
                        validCandidates.append(nbVar)
                    }
                }
            } else {
                // Need to decrease basicVar
                if coeff > .zero {
                    if lowerBounds[nbVar] == nil || nbVal > lowerBounds[nbVar]!.value {
                        validCandidates.append(nbVar)
                    }
                } else if coeff < .zero {
                    if upperBounds[nbVar] == nil || nbVal < upperBounds[nbVar]!.value {
                        validCandidates.append(nbVar)
                    }
                }
            }
        }

        return validCandidates.min() // Bland's anti-cycling rule
    }

/// Exact Farkas Lemma certificate of linear infeasibility.
/// Represents a non-negative linear combination of constraints yielding an inconsistent bound.
public struct FarkasCertificate: Sendable {
    public let multipliers: [(constraint: Expr, multiplier: Rational)]
    public let netConstant: Rational

    public init(multipliers: [(constraint: Expr, multiplier: Rational)], netConstant: Rational) {
        self.multipliers = multipliers
        self.netConstant = netConstant
    }
}

    /// Generate Farkas conflict certificate from an unpivotable row.
    public func buildFarkasConflict(violatingBasic: Int, isLowerViolation: Bool) -> [Expr] {
        var rawExplanation: [Expr] = []
        if isLowerViolation {
            if let lb = lowerBounds[violatingBasic] {
                rawExplanation.append(lb.reason)
            }
        } else {
            if let ub = upperBounds[violatingBasic] {
                rawExplanation.append(ub.reason)
            }
        }

        if let row = tableau[violatingBasic] {
            for (nbVar, coeff) in row {
                if isLowerViolation {
                    if coeff > .zero, let ub = upperBounds[nbVar] {
                        rawExplanation.append(ub.reason)
                    } else if coeff < .zero, let lb = lowerBounds[nbVar] {
                        rawExplanation.append(lb.reason)
                    }
                } else {
                    if coeff > .zero, let lb = lowerBounds[nbVar] {
                        rawExplanation.append(lb.reason)
                    } else if coeff < .zero, let ub = upperBounds[nbVar] {
                        rawExplanation.append(ub.reason)
                    }
                }
            }
        }

        // Deduplicate while preserving first appearance order
        var seen = Set<Expr>()
        var deduped: [Expr] = []
        for expr in rawExplanation {
            if !seen.contains(expr) {
                seen.insert(expr)
                deduped.append(expr)
            }
        }
        return deduped
    }

    /// Generate explicit linear Farkas multipliers proving infeasibility.
    public func generateFarkasCertificate(violatingBasic: Int, isLowerViolation: Bool) -> FarkasCertificate? {
        guard let row = tableau[violatingBasic] else { return nil }
        var multipliers: [(constraint: Expr, multiplier: Rational)] = []
        var netConstant = Rational.zero

        if isLowerViolation {
            guard let lb = lowerBounds[violatingBasic] else { return nil }
            multipliers.append((lb.reason, Rational(1)))
            netConstant = netConstant + lb.value

            for (nbVar, coeff) in row {
                if coeff > .zero {
                    guard let ub = upperBounds[nbVar] else { return nil }
                    multipliers.append((ub.reason, coeff))
                    netConstant = netConstant - coeff * ub.value
                } else if coeff < .zero {
                    guard let lbNb = lowerBounds[nbVar] else { return nil }
                    let mult = -coeff
                    multipliers.append((lbNb.reason, mult))
                    netConstant = netConstant + mult * lbNb.value
                }
            }
        } else {
            guard let ub = upperBounds[violatingBasic] else { return nil }
            multipliers.append((ub.reason, Rational(1)))
            netConstant = netConstant - ub.value

            for (nbVar, coeff) in row {
                if coeff > .zero {
                    guard let lbNb = lowerBounds[nbVar] else { return nil }
                    multipliers.append((lbNb.reason, coeff))
                    netConstant = netConstant + coeff * lbNb.value
                } else if coeff < .zero {
                    guard let ubNb = upperBounds[nbVar] else { return nil }
                    let mult = -coeff
                    multipliers.append((ubNb.reason, mult))
                    netConstant = netConstant - mult * ubNb.value
                }
            }
        }

        return FarkasCertificate(multipliers: multipliers, netConstant: netConstant)
    }

    // MARK: - Bounds Management

    /// Set an upper or lower bound on a variable.
    public func setBound(variable: Int, bound: BoundInfo, isLower: Bool) -> TheoryResult {
        let oldLower = lowerBounds[variable]
        let oldUpper = upperBounds[variable]

        if isLower {
            if let current = oldLower {
                if bound.value < current.value || (bound.value == current.value && (!bound.isStrict || current.isStrict)) {
                    return .consistent // Weaker than current bound
                }
            }
            if let currentUb = oldUpper {
                let clash = (bound.value > currentUb.value) || (bound.value == currentUb.value && (bound.isStrict || currentUb.isStrict))
                if clash {
                    let expl = [bound.reason, currentUb.reason]
                    isConflicted = true
                    conflictExplanation = expl
                    conflictScopeLevel = scopeLimits.count
                    return .conflict(explanation: expl)
                }
            }
            lowerBounds[variable] = bound
        } else {
            if let current = oldUpper {
                if bound.value > current.value || (bound.value == current.value && (!bound.isStrict || current.isStrict)) {
                    return .consistent // Weaker than current bound
                }
            }
            if let currentLb = oldLower {
                let clash = (bound.value < currentLb.value) || (bound.value == currentLb.value && (bound.isStrict || currentLb.isStrict))
                if clash {
                    let expl = [bound.reason, currentLb.reason]
                    isConflicted = true
                    conflictExplanation = expl
                    conflictScopeLevel = scopeLimits.count
                    return .conflict(explanation: expl)
                }
            }
            upperBounds[variable] = bound
        }

        undoHistory.append(BoundUndo(variable: variable, oldLower: oldLower, oldUpper: oldUpper))

        // If variable is non-basic and its current value violates the new bound, adjust it
        if nonBasicVars.contains(variable) {
            let val = values[variable] ?? .zero
            if isLower && val < bound.value {
                values[variable] = bound.value
            } else if !isLower && val > bound.value {
                values[variable] = bound.value
            }
            // Update all basic variables
            for bVar in basicVars {
                values[bVar] = computeRowValue(bVar)
            }
        }

        return checkFeasibility()
    }

    // MARK: - TheorySolver Conformance

    public func pushScope() {
        scopeLimits.append(undoHistory.count)
    }

    public func popScope() {
        guard let limit = scopeLimits.popLast() else { return }
        while undoHistory.count > limit {
            let undo = undoHistory.removeLast()
            lowerBounds[undo.variable] = undo.oldLower
            upperBounds[undo.variable] = undo.oldUpper
        }
        if let cLevel = conflictScopeLevel, cLevel > scopeLimits.count {
            isConflicted = false
            conflictExplanation = []
            conflictScopeLevel = nil
        }
        for bVar in basicVars {
            values[bVar] = computeRowValue(bVar)
        }
    }

    public func reset() {
        varCount = 0
        exprToVar.removeAll(keepingCapacity: true)
        varToExpr.removeAll(keepingCapacity: true)
        tableau.removeAll(keepingCapacity: true)
        basicVars.removeAll(keepingCapacity: true)
        nonBasicVars.removeAll(keepingCapacity: true)
        lowerBounds.removeAll(keepingCapacity: true)
        upperBounds.removeAll(keepingCapacity: true)
        values.removeAll(keepingCapacity: true)
        undoHistory.removeAll(keepingCapacity: true)
        scopeLimits.removeAll(keepingCapacity: true)
        assertedConstraints.removeAll(keepingCapacity: true)
        pendingDeductions.removeAll(keepingCapacity: true)
        isConflicted = false
        conflictExplanation = []
        conflictScopeLevel = nil
    }

    public func assertLiteral(_ literal: Expr) -> TheoryResult {
        return assertLiteral(literal, originalExpr: literal)
    }

    public func assertLiteral(_ literal: Expr, originalExpr: Expr) -> TheoryResult {
        assertedConstraints.append(originalExpr)

        // Parse linear constraint: e.g. x <= 5, x >= 0, x - y <= 2, x == y
        switch literal {
        case let .le(lhs, rhs):
            return assertInequality(lhs: lhs, rhs: rhs, isStrict: false, isGreater: false, originalExpr: originalExpr)
        case let .lt(lhs, rhs):
            return assertInequality(lhs: lhs, rhs: rhs, isStrict: true, isGreater: false, originalExpr: originalExpr)
        case let .ge(lhs, rhs):
            return assertInequality(lhs: lhs, rhs: rhs, isStrict: false, isGreater: true, originalExpr: originalExpr)
        case let .gt(lhs, rhs):
            return assertInequality(lhs: lhs, rhs: rhs, isStrict: true, isGreater: true, originalExpr: originalExpr)
        case let .eq(lhs, rhs):
            return assertEquality(lhs: lhs, rhs: rhs, originalExpr: originalExpr)
        case let .not(inner):
            // Invert condition
            switch inner {
            case let .le(lhs, rhs):
                return assertInequality(lhs: lhs, rhs: rhs, isStrict: true, isGreater: true, originalExpr: originalExpr)
            case let .lt(lhs, rhs):
                return assertInequality(lhs: lhs, rhs: rhs, isStrict: false, isGreater: true, originalExpr: originalExpr)
            case let .ge(lhs, rhs):
                return assertInequality(lhs: lhs, rhs: rhs, isStrict: true, isGreater: false, originalExpr: originalExpr)
            case let .gt(lhs, rhs):
                return assertInequality(lhs: lhs, rhs: rhs, isStrict: false, isGreater: false, originalExpr: originalExpr)
            case let .eq(lhs, rhs):
                var poly = toPolynomial(expr: lhs) - toPolynomial(expr: rhs)
                if let minVar = poly.terms.keys.min(), let leadingCoeff = poly.terms[minVar], leadingCoeff < .zero {
                    poly = poly * Rational(-1)
                }
                for bVar in basicVars {
                    if let row = tableau[bVar], row == poly.terms {
                        if let lb = lowerBounds[bVar], let ub = upperBounds[bVar], lb.value == ub.value, lb.value == -poly.constant {
                            return .conflict(explanation: [originalExpr, lb.reason, ub.reason])
                        }
                    }
                }
                return .consistent
            default:
                return .consistent
            }
        default:
            return .consistent
        }
    }

    private func assertEquality(lhs: Expr, rhs: Expr, originalExpr: Expr) -> TheoryResult {
        var poly = toPolynomial(expr: lhs) - toPolynomial(expr: rhs)

        if poly.terms.isEmpty {
            if poly.constant.isZero {
                return .consistent
            } else {
                return .conflict(explanation: [originalExpr])
            }
        }

        if let minVar = poly.terms.keys.min(), let leadingCoeff = poly.terms[minVar], leadingCoeff < .zero {
            poly = poly * Rational(-1)
        }

        if poly.terms.count == 1, let (v, coeff) = poly.terms.first {
            let boundVal = -poly.constant / coeff
            let bInfo = BoundInfo(value: boundVal, reason: originalExpr, isStrict: false)
            let r1 = setBound(variable: v, bound: bInfo, isLower: true)
            if case .conflict = r1 { return r1 }
            return setBound(variable: v, bound: bInfo, isLower: false)
        }

        var slackVar: Int? = nil
        for bVar in basicVars {
            if let row = tableau[bVar], row == poly.terms {
                slackVar = bVar
                break
            }
        }

        let s: Int
        if let existing = slackVar {
            s = existing
        } else {
            let slackExpr = Expr.variable(name: Symbol("slack_\(varCount)"), sort: .real)
            s = registerVariable(slackExpr)
            addRow(basicVar: s, terms: poly.terms)
        }

        let boundVal = -poly.constant
        let bInfo = BoundInfo(value: boundVal, reason: originalExpr, isStrict: false)
        let r1 = setBound(variable: s, bound: bInfo, isLower: true)
        if case .conflict = r1 { return r1 }
        return setBound(variable: s, bound: bInfo, isLower: false)
    }

    private func assertInequality(
        lhs: Expr,
        rhs: Expr,
        isStrict: Bool,
        isGreater: Bool,
        originalExpr: Expr
    ) -> TheoryResult {
        // Form: poly <= constant or poly >= constant
        var poly = toPolynomial(expr: lhs) - toPolynomial(expr: rhs)
        var effectiveStrict = isStrict
        var effectiveGreater = isGreater

        if poly.terms.isEmpty {
            // Constant inequality: e.g. 0 <= 5
            let isSatisfied = effectiveGreater
                ? (effectiveStrict ? -poly.constant > .zero : -poly.constant >= .zero)
                : (effectiveStrict ? poly.constant < .zero : poly.constant <= .zero)
            if !isSatisfied {
                return .conflict(explanation: [originalExpr])
            }
            return .consistent
        }

        if let minVar = poly.terms.keys.min(), let leadingCoeff = poly.terms[minVar], leadingCoeff < .zero {
            poly = poly * Rational(-1)
            effectiveGreater = !effectiveGreater
        }

        if poly.terms.count == 1, let (v, coeff) = poly.terms.first {
            // Single variable bound: coeff * x + c <= 0 <=> coeff * x <= -c
            let boundVal = -poly.constant / coeff
            let isLower = (coeff > .zero && effectiveGreater) || (coeff < .zero && !effectiveGreater)
            let boundInfo = BoundInfo(value: boundVal, reason: originalExpr, isStrict: effectiveStrict)
            return setBound(variable: v, bound: boundInfo, isLower: isLower)
        }

        var slackVar: Int? = nil
        for bVar in basicVars {
            if let row = tableau[bVar], row == poly.terms {
                slackVar = bVar
                break
            }
        }

        let s: Int
        if let existing = slackVar {
            s = existing
        } else {
            let slackExpr = Expr.variable(name: Symbol("slack_\(varCount)"), sort: .real)
            s = registerVariable(slackExpr)
            addRow(basicVar: s, terms: poly.terms)
        }

        let boundVal = -poly.constant
        let boundInfo = BoundInfo(value: boundVal, reason: originalExpr, isStrict: effectiveStrict)
        return setBound(variable: s, bound: boundInfo, isLower: effectiveGreater)
    }

    private func toPolynomial(expr: Expr) -> LinearPolynomial {
        switch expr {
        case let .realConst(r):
            return LinearPolynomial(constant: r)
        case let .intConst(i):
            return LinearPolynomial(constant: Rational(i))
        case .variable:
            let v = registerVariable(expr)
            return LinearPolynomial(terms: [v: Rational(1)], constant: .zero)
        case let .add(terms):
            var poly = LinearPolynomial()
            for t in terms {
                poly = poly + toPolynomial(expr: t)
            }
            return poly
        case let .sub(a, b):
            return toPolynomial(expr: a) - toPolynomial(expr: b)
        case let .mul(terms):
            // Linear multiplication: constant * expr
            var constFactor = Rational(1)
            var varPoly = LinearPolynomial()
            var hasVar = false
            for t in terms {
                let p = toPolynomial(expr: t)
                if p.terms.isEmpty {
                    constFactor = constFactor * p.constant
                } else if !hasVar {
                    varPoly = p
                    hasVar = true
                }
            }
            if hasVar {
                return varPoly * constFactor
            } else {
                return LinearPolynomial(constant: constFactor)
            }
        case let .neg(inner):
            return toPolynomial(expr: inner) * Rational(-1)
        default:
            let v = registerVariable(expr)
            return LinearPolynomial(terms: [v: Rational(1)], constant: .zero)
        }
    }

    /// Perform bound propagation across tableau rows to derive new bounds and shared equalities.
    public func propagateBounds() -> [TheoryDeduction] {
        var deductions: [TheoryDeduction] = []

        for bVar in basicVars {
            guard let row = tableau[bVar], let bExpr = varToExpr[bVar] else { continue }

            // 1. Check if all non-basic variables have lower bounds (for a_ij > 0) and upper bounds (for a_ij < 0)
            var canComputeLower = true
            var impliedLb = Rational.zero
            var lbReasons: [Expr] = []

            for (nbVar, coeff) in row {
                if coeff > .zero {
                    if let lb = lowerBounds[nbVar] {
                        impliedLb = impliedLb + coeff * lb.value
                        lbReasons.append(lb.reason)
                    } else {
                        canComputeLower = false
                        break
                    }
                } else if coeff < .zero {
                    if let ub = upperBounds[nbVar] {
                        impliedLb = impliedLb + coeff * ub.value
                        lbReasons.append(ub.reason)
                    } else {
                        canComputeLower = false
                        break
                    }
                }
            }

            if canComputeLower {
                let currentLb = lowerBounds[bVar]?.value
                if currentLb == nil || impliedLb > currentLb! {
                    let deducedExpr = Expr.ge(bExpr, .realConst(impliedLb))
                    deductions.append(TheoryDeduction(literal: deducedExpr, explanation: lbReasons))
                }
            }

            // 2. Check if all non-basic variables have upper bounds (for a_ij > 0) and lower bounds (for a_ij < 0)
            var canComputeUpper = true
            var impliedUb = Rational.zero
            var ubReasons: [Expr] = []

            for (nbVar, coeff) in row {
                if coeff > .zero {
                    if let ub = upperBounds[nbVar] {
                        impliedUb = impliedUb + coeff * ub.value
                        ubReasons.append(ub.reason)
                    } else {
                        canComputeUpper = false
                        break
                    }
                } else if coeff < .zero {
                    if let lb = lowerBounds[nbVar] {
                        impliedUb = impliedUb + coeff * lb.value
                        ubReasons.append(lb.reason)
                    } else {
                        canComputeUpper = false
                        break
                    }
                }
            }

            if canComputeUpper {
                let currentUb = upperBounds[bVar]?.value
                if currentUb == nil || impliedUb < currentUb! {
                    let deducedExpr = Expr.le(bExpr, .realConst(impliedUb))
                    deductions.append(TheoryDeduction(literal: deducedExpr, explanation: ubReasons))
                }
            }

            // 3. Implied equality between variables: if x_i has lb == ub, emit equality
            if let lb = lowerBounds[bVar], let ub = upperBounds[bVar], lb.value == ub.value {
                let fixedVal = lb.value
                let eqExpr = Expr.eq(bExpr, .realConst(fixedVal))
                deductions.append(TheoryDeduction(literal: eqExpr, explanation: [lb.reason, ub.reason]))

                if fixedVal.isZero, let row = tableau[bVar], row.count == 2 {
                    let sortedTerms = row.sorted { $0.key < $1.key }
                    let (v1, c1) = sortedTerms[0]
                    let (v2, c2) = sortedTerms[1]
                    if c1 == -c2, let e1 = varToExpr[v1], let e2 = varToExpr[v2] {
                        let varEq = Expr.eq(e1, e2)
                        deductions.append(TheoryDeduction(literal: varEq, explanation: [lb.reason, ub.reason]))
                    }
                }
            }
        }

        return deductions
    }

    public func checkConsistency() -> TheoryResult {
        return checkFeasibility()
    }

    public func propagateDeductions() -> [TheoryDeduction] {
        var deds = pendingDeductions
        pendingDeductions.removeAll(keepingCapacity: true)
        deds.append(contentsOf: propagateBounds())
        return deds
    }

    public func collectSharedTerms() -> [Expr] {
        return Array(exprToVar.keys)
    }

    public func variableValue(_ expr: Expr) -> Rational? {
        guard let v = exprToVar[expr] else { return nil }
        return values[v]
    }
}

// MARK: - LinearPolynomial Arithmetic

private func + (lhs: LinearPolynomial, rhs: LinearPolynomial) -> LinearPolynomial {
    var terms = lhs.terms
    for (v, coeff) in rhs.terms {
        let sum = (terms[v] ?? .zero) + coeff
        if sum.isZero {
            terms.removeValue(forKey: v)
        } else {
            terms[v] = sum
        }
    }
    return LinearPolynomial(terms: terms, constant: lhs.constant + rhs.constant)
}

private func - (lhs: LinearPolynomial, rhs: LinearPolynomial) -> LinearPolynomial {
    return lhs + (rhs * Rational(-1))
}

private func * (lhs: LinearPolynomial, rhs: Rational) -> LinearPolynomial {
    var terms: [Int: Rational] = [:]
    for (v, coeff) in lhs.terms {
        let prod = coeff * rhs
        if !prod.isZero {
            terms[v] = prod
        }
    }
    return LinearPolynomial(terms: terms, constant: lhs.constant * rhs)
}
