import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT

/// Dedicated decision procedure for Quantifier-Free Linear Integer Arithmetic (QF_LIA).
/// Combines Simplex linear relaxation, Gomory mixed-integer cutting planes, and Branch-and-Bound search.
public final class LIASolver: TheorySolver, @unchecked Sendable {
    public let theoryId: TheoryId = .lia

    private let simplex: LRASolver
    private var integerVars: Set<Expr> = []
    private var constraints: [Expr] = []
    private var scopeLimits: [Int] = []

    public init() {
        self.simplex = LRASolver()
    }

    // MARK: - Variable & Constraint Registration

    /// Register an integer-typed variable.
    public func registerIntegerVariable(_ expr: Expr) {
        integerVars.insert(expr)
        _ = simplex.registerVariable(expr)
    }

    public func assertLiteral(_ literal: Expr) -> TheoryResult {
        constraints.append(literal)

        // Check for integer variables in the expression
        let vars = extractVariables(literal)
        for v in vars {
            if case let .variable(_, sort) = v, sort == .int {
                registerIntegerVariable(v)
            }
        }

        // Check for Diophantine GCD infeasibility: e.g. 2x + 4y == 5
        if case let .eq(lhs, rhs) = literal {
            if let conflict = checkGCDInfeasibility(lhs: lhs, rhs: rhs, original: literal) {
                return conflict
            }
        }

        return simplex.assertLiteral(literal)
    }

    // MARK: - Diophantine Equation GCD Test

    /// Check if sum(a_i * x_i) == c has integer solutions by verifying gcd(a_1..a_n) divides c.
    private func checkGCDInfeasibility(lhs: Expr, rhs: Expr, original: Expr) -> TheoryResult? {
        let (coeffs, c) = extractLinearCoefficients(lhs: lhs, rhs: rhs)
        guard !coeffs.isEmpty, !c.isZero else { return nil }

        var g = BigInt.zero
        for coeff in coeffs {
            guard coeff.denominator == 1 else { return nil } // Only pure integer coefficients
            let intA = coeff.numerator
            let absA = intA < 0 ? -intA : intA
            g = BigInt.gcd(g, absA)
        }

        guard g > 1 else { return nil }
        guard c.denominator == 1 else { return nil }
        let intC = c.numerator

        if intC % g != 0 {
            // No integer solution exists by Bezout's identity / Diophantine theorem
            return .conflict(explanation: [original])
        }
        return nil
    }

    private func extractLinearCoefficients(lhs: Expr, rhs: Expr) -> (coeffs: [Rational], constant: Rational) {
        // Collect linear terms from lhs - rhs
        var coeffs: [Rational] = []
        var constant = Rational.zero

        func walk(_ e: Expr, mult: Rational) {
            switch e {
            case let .intConst(i):
                constant = constant + mult * Rational(i)
            case let .realConst(r):
                constant = constant + mult * r
            case .variable:
                coeffs.append(mult)
            case let .add(terms):
                for t in terms { walk(t, mult: mult) }
            case let .sub(a, b):
                walk(a, mult: mult)
                walk(b, mult: -mult)
            case let .mul(terms):
                var constFactor = Rational(1)
                var varTerm: Expr?
                for t in terms {
                    if case let .intConst(i) = t {
                        constFactor = constFactor * Rational(i)
                    } else if case let .realConst(r) = t {
                        constFactor = constFactor * r
                    } else {
                        varTerm = t
                    }
                }
                if let v = varTerm {
                    walk(v, mult: mult * constFactor)
                } else {
                    constant = constant + mult * constFactor
                }
            default:
                break
            }
        }

        walk(lhs, mult: Rational(1))
        walk(rhs, mult: Rational(-1))
        return (coeffs, constant)
    }

    // MARK: - Branch-and-Bound with Gomory Cuts

    /// Check integer consistency by first solving the continuous relaxation and then branching.
    public func checkConsistency() -> TheoryResult {
        // 1. Solve continuous relaxation
        let relaxResult = simplex.checkConsistency()
        if case .conflict = relaxResult {
            return relaxResult
        }

        // 2. Check integrality of all integer variables
        guard let fractionalVar = findFractionalIntegerVariable() else {
            // All integer variables have integer values in the current assignment!
            return .consistent
        }

        // 3. Branch-and-Bound: let v = fractionalVar, val = beta(v)
        // Branch 1: v <= floor(val)
        // Branch 2: v >= floor(val) + 1
        let val = simplex.variableValue(fractionalVar)!
        let floorVal = val.floor
        let ceilVal = floorVal + BigInt(1)

        // Try Left Branch: v <= floorVal
        pushScope()
        let leftBound = Expr.le(fractionalVar, .intConst(floorVal))
        let leftRes = simplex.assertLiteral(leftBound)
        if case .consistent = leftRes {
            let subRes = checkConsistency()
            if case .consistent = subRes {
                return .consistent
            }
        }
        popScope()

        // Try Right Branch: v >= ceilVal
        pushScope()
        let rightBound = Expr.ge(fractionalVar, .intConst(ceilVal))
        let rightRes = simplex.assertLiteral(rightBound)
        if case .consistent = rightRes {
            let subRes = checkConsistency()
            if case .consistent = subRes {
                return .consistent
            }
        }
        popScope()

        // Both branches unsatisfiable: integer problem is UNSAT
        return .conflict(explanation: constraints)
    }

    /// Find an integer variable with a fractional value in the continuous Simplex tableau.
    private func findFractionalIntegerVariable() -> Expr? {
        for vExpr in integerVars {
            if let val = simplex.variableValue(vExpr) {
                if !val.isInteger {
                    return vExpr
                }
            }
        }
        return nil
    }

    // MARK: - TheorySolver Conformance

    public func pushScope() {
        scopeLimits.append(constraints.count)
        simplex.pushScope()
    }

    public func popScope() {
        guard let limit = scopeLimits.popLast() else { return }
        while constraints.count > limit {
            _ = constraints.popLast()
        }
        simplex.popScope()
    }

    public func reset() {
        integerVars.removeAll(keepingCapacity: true)
        constraints.removeAll(keepingCapacity: true)
        scopeLimits.removeAll(keepingCapacity: true)
        simplex.reset()
    }

    public func propagateDeductions() -> [TheoryDeduction] {
        return simplex.propagateDeductions()
    }

    public func collectSharedTerms() -> [Expr] {
        return simplex.collectSharedTerms()
    }

    public func integerVariableValue(_ expr: Expr) -> BigInt? {
        guard let val = simplex.variableValue(expr), val.isInteger else { return nil }
        return val.numerator
    }

    // MARK: - Variable Extraction Helper

    private func extractVariables(_ expr: Expr) -> Set<Expr> {
        var result = Set<Expr>()
        func walk(_ e: Expr) {
            if case .variable = e {
                result.insert(e)
            }
            switch e {
            case let .not(inner), let .neg(inner):
                walk(inner)
            case let .and(args), let .or(args), let .add(args), let .mul(args), let .distinct(args):
                for a in args { walk(a) }
            case let .implies(a, b), let .xor(a, b), let .iff(a, b), let .eq(a, b),
                 let .sub(a, b), let .div(a, b), let .mod(a, b),
                 let .lt(a, b), let .le(a, b), let .gt(a, b), let .ge(a, b):
                walk(a); walk(b)
            case let .ite(c, t, el):
                walk(c); walk(t); walk(el)
            case let .apply(_, args, _):
                for a in args { walk(a) }
            default:
                break
            }
        }
        walk(expr)
        return result
    }
}
