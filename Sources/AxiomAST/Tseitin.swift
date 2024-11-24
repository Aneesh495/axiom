import Foundation
import AxiomCore

/// Equisatisfiable CNF formula representation output by Tseitin transformation
public struct CNFFormula: Sendable {
    /// Total number of variables allocated
    public var numVariables: Int

    /// Clauses represented as arrays of signed integer literals (1-based, negative indicates negation)
    public var clauses: [[Int32]]

    /// Mapping from SAT variable index to original AST expression
    public var varToExpr: [Int32: Expr]

    /// Mapping from AST expression to SAT variable index
    public var exprToVar: [Expr: Int32]

    public init() {
        self.numVariables = 0
        self.clauses = []
        self.varToExpr = [:]
        self.exprToVar = [:]
    }
}

/// Polarity-aware Plaisted-Greenbaum Tseitin transformation converting first-order boolean formulas
/// into equisatisfiable Conjunctive Normal Form (CNF) in linear time O(n).
public final class TseitinTransformer: @unchecked Sendable {
    public enum Polarity {
        case positive
        case negative
        case both

        public var hasPositive: Bool { self == .positive || self == .both }
        public var hasNegative: Bool { self == .negative || self == .both }

        public func inverted() -> Polarity {
            switch self {
            case .positive: return .negative
            case .negative: return .positive
            case .both: return .both
            }
        }
    }

    private var nextVarId: Int32 = 1
    private var formula = CNFFormula()
    private var visitedPolarity: [Expr: Polarity] = [:]

    public init() {}

    /// Transform an AST expression into equisatisfiable CNF, asserting that the root formula must hold true
    public func transform(_ root: Expr) -> CNFFormula {
        formula = CNFFormula()
        nextVarId = 1
        visitedPolarity.removeAll(keepingCapacity: true)

        let rootLit = encode(root, polarity: .positive)
        // Assert top-level root literal: [rootLit]
        formula.clauses.append([rootLit])
        formula.numVariables = Int(nextVarId - 1)

        return formula
    }

    /// Allocate or retrieve a fresh propositional literal for an expression
    private func getOrCreateVar(for expr: Expr) -> Int32 {
        if let existing = formula.exprToVar[expr] {
            return existing
        }
        let v = nextVarId
        nextVarId += 1
        formula.exprToVar[expr] = v
        formula.varToExpr[v] = expr
        return v
    }

    private func encode(_ expr: Expr, polarity: Polarity) -> Int32 {
        switch expr {
        case let .boolConst(b):
            let v = getOrCreateVar(for: expr)
            formula.clauses.append([b ? v : -v])
            return b ? v : -v

        case .variable, .eq, .distinct, .apply, .lt, .le, .gt, .ge,
             .bvULt, .bvULe, .bvSLt, .bvSLe:
            // Atomic propositions or theory predicates
            return getOrCreateVar(for: expr)

        case let .not(inner):
            let innerLit = encode(inner, polarity: polarity.inverted())
            return -innerLit

        case let .and(args):
            if args.isEmpty {
                return encode(.boolConst(true), polarity: polarity)
            }
            let p = getOrCreateVar(for: expr)
            let childLits = args.map { encode($0, polarity: polarity) }

            // Plaisted-Greenbaum polarity optimization:
            // Positive polarity: p => (l1 and l2 and ... and ln)
            // Clauses: (~p or l1), (~p or l2), ..., (~p or ln)
            if polarity.hasPositive {
                for lit in childLits {
                    formula.clauses.append([-p, lit])
                }
            }

            // Negative polarity: (l1 and l2 and ... and ln) => p
            // Clause: (~l1 or ~l2 or ... or ~ln or p)
            if polarity.hasNegative {
                var clause = childLits.map { -$0 }
                clause.append(p)
                formula.clauses.append(clause)
            }
            return p

        case let .or(args):
            if args.isEmpty {
                return encode(.boolConst(false), polarity: polarity)
            }
            let p = getOrCreateVar(for: expr)
            let childLits = args.map { encode($0, polarity: polarity) }

            // Positive polarity: p => (l1 or l2 or ... or ln)
            // Clause: (~p or l1 or l2 or ... or ln)
            if polarity.hasPositive {
                var clause = childLits
                clause.append(-p)
                formula.clauses.append(clause)
            }

            // Negative polarity: (l1 or l2 or ... or ln) => p
            // Clauses: (~l1 or p), (~l2 or p), ..., (~ln or p)
            if polarity.hasNegative {
                for lit in childLits {
                    formula.clauses.append([-lit, p])
                }
            }
            return p

        case let .implies(lhs, rhs):
            return encode(.or([.not(lhs), rhs]), polarity: polarity)

        case let .xor(lhs, rhs):
            let p = getOrCreateVar(for: expr)
            let l = encode(lhs, polarity: .both)
            let r = encode(rhs, polarity: .both)

            // p <=> (l xor r)
            formula.clauses.append([-p, -l, -r])
            formula.clauses.append([-p, l, r])
            formula.clauses.append([p, -l, r])
            formula.clauses.append([p, l, -r])
            return p

        case let .iff(lhs, rhs):
            let p = getOrCreateVar(for: expr)
            let l = encode(lhs, polarity: .both)
            let r = encode(rhs, polarity: .both)

            // p <=> (l <=> r)
            formula.clauses.append([-p, -l, r])
            formula.clauses.append([-p, l, -r])
            formula.clauses.append([p, l, r])
            formula.clauses.append([p, -l, -r])
            return p

        case let .ite(cond, thenB, elseB):
            let p = getOrCreateVar(for: expr)
            let c = encode(cond, polarity: .both)
            let t = encode(thenB, polarity: polarity)
            let e = encode(elseB, polarity: polarity)

            if polarity.hasPositive {
                formula.clauses.append([-c, -p, t])
                formula.clauses.append([c, -p, e])
            }
            if polarity.hasNegative {
                formula.clauses.append([-c, p, -t])
                formula.clauses.append([c, p, -e])
            }
            return p

        default:
            return getOrCreateVar(for: expr)
        }
    }
}
