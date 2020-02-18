import Foundation
import AxiomCore
import AxiomAST
import AxiomSMT

/// Result of Bounded Model Checking (BMC).
public enum BMCResult: CustomStringConvertible, Sendable {
    /// No violation found within the unwinding bound k
    case safe(bound: Int, unwindingComplete: Bool)

    /// A safety violation counterexample trace found at step depth
    case violation(step: Int, model: SMTModel, assertion: Expr)

    public var description: String {
        switch self {
        case let .safe(bound, complete):
            let cStr = complete ? " (complete proof)" : " (bounded)"
            return "BMC Safe up to bound \(bound)\(cStr)"
        case let .violation(step, model, assertion):
            return "BMC Violation at step \(step) for assertion \(assertion)\n\(model)"
        }
    }
}

/// Bounded Model Checker (BMC) unrolling loops and function recursion up to depth k.
/// Encodes execution paths into Static Single Assignment (SSA) form solved via SMT.
public final class BMC: @unchecked Sendable {
    private let solver: SMTSolver
    private var versionCounter: [Symbol: Int]
    private var variableSorts: [Symbol: Sort]
    private var ssaFormulas: [Expr]

    public init() {
        self.solver = SMTSolver()
        self.versionCounter = [:]
        self.variableSorts = [:]
        self.ssaFormulas = []
    }

    /// Run Bounded Model Checking on a procedure up to unwinding bound k.
    public func check(procedure: Procedure, bound: Int) -> BMCResult {
        solver.reset()
        versionCounter.removeAll(keepingCapacity: true)
        variableSorts.removeAll(keepingCapacity: true)
        ssaFormulas.removeAll(keepingCapacity: true)

        // 1. Assert preconditions
        for req in procedure.requires {
            _ = solver.assert(req)
        }

        // 2. Unroll the procedure body up to bound k
        let unrolled = unroll(stmt: procedure.body, bound: bound)

        // 3. Convert unrolled body to SSA and check assertions
        let (pathCond, assertions) = encodeSSA(stmt: unrolled, pathCondition: .boolConst(true))

        // Assert all SSA assignment equations into SMT solver
        for eq in ssaFormulas {
            _ = solver.assert(eq)
        }

        // 4. Check each safety assertion along its path condition
        for (idx, (cond, assertion)) in assertions.enumerated() {
            solver.push()

            // Violation check: pathCondition /\ not(assertion)
            let violationExpr = Expr.and([cond, .not(assertion)])
            _ = solver.assert(violationExpr)

            let res = solver.check()
            if res == .sat {
                let model = solver.getModel() ?? SMTModel()
                solver.pop()
                return .violation(step: idx, model: model, assertion: assertion)
            }

            solver.pop()
        }

        // 5. Check postconditions
        for post in procedure.ensures {
            solver.push()
            let currentPost = mapToCurrentSSAVariables(post)
            let violationExpr = Expr.and([pathCond, .not(currentPost)])
            _ = solver.assert(violationExpr)

            let res = solver.check()
            if res == .sat {
                let model = solver.getModel() ?? SMTModel()
                solver.pop()
                return .violation(step: assertions.count, model: model, assertion: post)
            }

            solver.pop()
        }

        return .safe(bound: bound, unwindingComplete: false)
    }

    // MARK: - Loop Unrolling

    private func unroll(stmt: Stmt, bound: Int) -> Stmt {
        switch stmt {
        case .skip, .assign, .assert, .assume, .havoc, .load, .store, .alloc, .free:
            return stmt

        case let .seq(stmts):
            return .seq(stmts.map { unroll(stmt: $0, bound: bound) })

        case let .ifThenElse(c, t, e):
            return .ifThenElse(
                condition: c,
                thenBranch: unroll(stmt: t, bound: bound),
                elseBranch: unroll(stmt: e, bound: bound)
            )

        case let .whileLoop(cond, _, body):
            // Unroll loop up to bound iterations sequentially
            let unrolledBody = unroll(stmt: body, bound: bound)
            var unrolledStmts: [Stmt] = []
            for _ in 0..<bound {
                unrolledStmts.append(
                    .ifThenElse(
                        condition: cond,
                        thenBranch: unrolledBody,
                        elseBranch: .skip
                    )
                )
            }
            unrolledStmts.append(.assume(condition: .not(cond)))
            return .seq(unrolledStmts)
        }
    }

    // MARK: - SSA Encoding

    private func encodeSSA(stmt: Stmt, pathCondition: Expr) -> (finalPathCondition: Expr, assertions: [(condition: Expr, assertion: Expr)]) {
        switch stmt {
        case .skip:
            return (pathCondition, [])

        case let .assign(variable, value):
            variableSorts[variable] = value.sort
            let currentVal = mapToCurrentSSAVariables(value)
            let nextVer = (versionCounter[variable] ?? 0) + 1
            versionCounter[variable] = nextVer

            let ssaVar = Expr.variable(name: Symbol("\(variable.name)_\(nextVer)"), sort: value.sort)
            ssaFormulas.append(Expr.eq(ssaVar, currentVal))
            return (pathCondition, [])

        case let .seq(stmts):
            var currentPath = pathCondition
            var collectedAssertions: [(condition: Expr, assertion: Expr)] = []
            for s in stmts {
                let (nextPath, assertions) = encodeSSA(stmt: s, pathCondition: currentPath)
                currentPath = nextPath
                collectedAssertions.append(contentsOf: assertions)
            }
            return (currentPath, collectedAssertions)

        case let .ifThenElse(cond, thenBranch, elseBranch):
            let ssaCond = mapToCurrentSSAVariables(cond)
            let stateBefore = versionCounter

            let thenPath = Expr.and([pathCondition, ssaCond])
            let (_, thenAss) = encodeSSA(stmt: thenBranch, pathCondition: thenPath)
            let stateAfterThen = versionCounter

            versionCounter = stateBefore
            let elsePath = Expr.and([pathCondition, .not(ssaCond)])
            let (_, elseAss) = encodeSSA(stmt: elseBranch, pathCondition: elsePath)
            let stateAfterElse = versionCounter

            // Phi-node join for modified variables
            let joinedVars = Set(stateAfterThen.keys).union(stateAfterElse.keys)
            for v in joinedVars {
                let verThen = stateAfterThen[v] ?? stateBefore[v] ?? 0
                let verElse = stateAfterElse[v] ?? stateBefore[v] ?? 0
                if verThen != verElse {
                    let nextVer = max(verThen, verElse) + 1
                    versionCounter[v] = nextVer

                    let s = variableSorts[v] ?? .int
                    let varThen = Expr.variable(name: Symbol("\(v.name)_\(verThen)"), sort: s)
                    let varElse = Expr.variable(name: Symbol("\(v.name)_\(verElse)"), sort: s)
                    let varJoin = Expr.variable(name: Symbol("\(v.name)_\(nextVer)"), sort: s)

                    ssaFormulas.append(Expr.implies(ssaCond, Expr.eq(varJoin, varThen)))
                    ssaFormulas.append(Expr.implies(Expr.not(ssaCond), Expr.eq(varJoin, varElse)))
                }
            }

            return (pathCondition, thenAss + elseAss)

        case let .assert(assertion, _):
            let ssaAss = mapToCurrentSSAVariables(assertion)
            return (pathCondition, [(condition: pathCondition, assertion: ssaAss)])

        case let .assume(condition):
            let ssaCond = mapToCurrentSSAVariables(condition)
            return (Expr.and([pathCondition, ssaCond]), [])

        default:
            return (pathCondition, [])
        }
    }

    private func mapToCurrentSSAVariables(_ expr: Expr) -> Expr {
        switch expr {
        case let .variable(name, sort):
            if let ver = versionCounter[name] {
                return .variable(name: Symbol("\(name.name)_\(ver)"), sort: sort)
            }
            return expr

        case let .not(child):
            return .not(mapToCurrentSSAVariables(child))

        case let .and(children):
            return .and(children.map { mapToCurrentSSAVariables($0) })

        case let .or(children):
            return .or(children.map { mapToCurrentSSAVariables($0) })

        case let .eq(lhs, rhs):
            return .eq(mapToCurrentSSAVariables(lhs), mapToCurrentSSAVariables(rhs))

        case let .add(args):
            return .add(args.map { mapToCurrentSSAVariables($0) })

        case let .sub(lhs, rhs):
            return .sub(mapToCurrentSSAVariables(lhs), mapToCurrentSSAVariables(rhs))

        case let .mul(args):
            return .mul(args.map { mapToCurrentSSAVariables($0) })

        case let .le(lhs, rhs):
            return .le(mapToCurrentSSAVariables(lhs), mapToCurrentSSAVariables(rhs))

        case let .lt(lhs, rhs):
            return .lt(mapToCurrentSSAVariables(lhs), mapToCurrentSSAVariables(rhs))

        case let .ge(lhs, rhs):
            return .ge(mapToCurrentSSAVariables(lhs), mapToCurrentSSAVariables(rhs))

        case let .gt(lhs, rhs):
            return .gt(mapToCurrentSSAVariables(lhs), mapToCurrentSSAVariables(rhs))

        default:
            return expr
        }
    }
}
