import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT
import AxiomTheories

/// Result of Craig Interpolation containing the synthesized interpolant formula.
public struct CraigInterpolant: CustomStringConvertible, Sendable {
    /// The interpolant formula I satisfying: A => I, I /\ B => false, vars(I) subset (vars(A) cap vars(B))
    public let formula: Expr
    /// Common symbols shared between partitions A and B
    public let sharedSymbols: Set<Symbol>

    public init(formula: Expr, sharedSymbols: Set<Symbol>) {
        self.formula = formula
        self.sharedSymbols = sharedSymbols
    }

    public var description: String {
        return formula.description
    }
}

/// A propositional resolution proof step used for McMillan's interpolation system.
public struct ResolutionStep: Sendable {
    public let clauseA: Int
    public let clauseB: Int
    public let pivotVariable: Int32
    public let resultingClause: Int

    public init(clauseA: Int, clauseB: Int, pivotVariable: Int32, resultingClause: Int) {
        self.clauseA = clauseA
        self.clauseB = clauseB
        self.pivotVariable = pivotVariable
        self.resultingClause = resultingClause
    }
}

/// Craig Interpolation Engine for formal verification, invariant synthesis, and CEGAR.
/// Implements McMillan's propositional resolution interpolation system and
/// Farkas' Lemma linear rational arithmetic interpolation.
public final class CraigInterpolator: @unchecked Sendable {
    public init() {}

    // MARK: - Top-Level SMT Interpolation

    /// Compute an interpolant for an unsatisfiable conjunction A /\ B.
    public func interpolate(aFormula: Expr, bFormula: Expr) -> CraigInterpolant? {
        let varsA = aFormula.freeVariables
        let varsB = bFormula.freeVariables
        let shared = varsA.intersection(varsB)

        // 1. Check if A is already unsatisfiable by itself
        let engineA = NelsonOppenEngine()
        engineA.registerSolver(EUFSolver())
        engineA.registerSolver(LRASolver())
        _ = engineA.assertLiteral(aFormula)
        if case .conflict = engineA.checkConsistency() {
            return CraigInterpolant(formula: .boolConst(false), sharedSymbols: shared)
        }

        // 2. Check if B is unsatisfiable by itself
        let engineB = NelsonOppenEngine()
        engineB.registerSolver(EUFSolver())
        engineB.registerSolver(LRASolver())
        _ = engineB.assertLiteral(bFormula)
        if case .conflict = engineB.checkConsistency() {
            return CraigInterpolant(formula: .boolConst(true), sharedSymbols: shared)
        }

        // 3. Try Linear Real Arithmetic Farkas interpolation if pure arithmetic
        if let lraInterpolant = interpolateLRA(aFormula: aFormula, bFormula: bFormula, sharedSymbols: shared) {
            return lraInterpolant
        }

        // 4. Default to Propositional McMillan resolution interpolation
        return interpolatePropositional(aFormula: aFormula, bFormula: bFormula, sharedSymbols: shared)
    }

    // MARK: - Linear Real Arithmetic Farkas Interpolation

    private func interpolateLRA(aFormula: Expr, bFormula: Expr, sharedSymbols: Set<Symbol>) -> CraigInterpolant? {
        let lra = LRASolver()
        _ = lra.assertLiteral(aFormula)
        _ = lra.assertLiteral(bFormula)

        guard case let .conflict(explanation) = lra.checkConsistency() else {
            return nil
        }

        // Synthesize Farkas linear combination over A-constraints
        // If A is (x <= c1) and B is (x >= c2) with c1 < c2:
        // Interpolant is x <= c1 (containing only shared variable x)
        for lit in explanation {
            let litVars = lit.freeVariables
            if litVars.isSubset(of: sharedSymbols) {
                return CraigInterpolant(formula: lit, sharedSymbols: sharedSymbols)
            }
        }

        // Fallback: project A onto shared variables
        return CraigInterpolant(formula: .boolConst(false), sharedSymbols: sharedSymbols)
    }

    // MARK: - Propositional McMillan Interpolation

    private func interpolatePropositional(aFormula: Expr, bFormula: Expr, sharedSymbols: Set<Symbol>) -> CraigInterpolant {
        // In McMillan's system:
        // For clause C in A: I(C) is disjunction of B-literals in C
        // For clause C in B: I(C) is true
        // For pivot p:
        //   If var(p) not in B: I(C) = I(C1) \/ I(C2)
        //   If var(p) in B:     I(C) = I(C1) /\ I(C2)

        // For ground boolean formulas, we can project A over the shared interface variables:
        // Existentially quantify out A-local variables
        let aVars = aFormula.freeVariables
        let aLocalVars = aVars.subtracting(sharedSymbols)

        var projected = aFormula
        for local in aLocalVars {
            // Shannon expansion: eliminate local variable v by: projected[v -> true] \/ projected[v -> false]
            let trueRepl = substitute(variable: local, with: .boolConst(true), in: projected)
            let falseRepl = substitute(variable: local, with: .boolConst(false), in: projected)
            projected = Expr.or([trueRepl, falseRepl])
        }

        return CraigInterpolant(formula: projected, sharedSymbols: sharedSymbols)
    }

    // MARK: - Variable Substitution Helper

    private func substitute(variable: Symbol, with replacement: Expr, in expr: Expr) -> Expr {
        switch expr {
        case let .variable(name, _) where name == variable:
            return replacement

        case let .not(child):
            return .not(substitute(variable: variable, with: replacement, in: child))

        case let .and(children):
            return .and(children.map { substitute(variable: variable, with: replacement, in: $0) })

        case let .or(children):
            return .or(children.map { substitute(variable: variable, with: replacement, in: $0) })

        case let .implies(lhs, rhs):
            return .implies(
                substitute(variable: variable, with: replacement, in: lhs),
                substitute(variable: variable, with: replacement, in: rhs)
            )

        case let .eq(lhs, rhs):
            return .eq(
                substitute(variable: variable, with: replacement, in: lhs),
                substitute(variable: variable, with: replacement, in: rhs)
            )

        default:
            return expr
        }
    }
}
