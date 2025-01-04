import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT

/// E-node signature identifying an uninterpreted function application by function symbol and argument E-class IDs.
public struct ENodeSignature: Hashable, Sendable {
    public let symbol: Symbol
    public let argClasses: [Int]

    public init(symbol: Symbol, argClasses: [Int]) {
        self.symbol = symbol
        self.argClasses = argClasses
    }
}

/// A node in the EUF E-graph representing a term or subterm.
public final class ENode: @unchecked Sendable {
    public let id: Int
    public let term: Expr
    public var classId: Int
    public var parents: [Int] // IDs of ENodes that have this node's class as an argument

    public init(id: Int, term: Expr) {
        self.id = id
        self.term = term
        self.classId = id
        self.parents = []
    }
}

/// Proof step representing an edge in the congruence closure explanation forest.
public struct EUFProofEdge: Sendable {
    public let source: Int
    public let target: Int
    public let reason: Expr // The asserted equality or congruence step

    public init(source: Int, target: Int, reason: Expr) {
        self.source = source
        self.target = target
        self.reason = reason
    }
}

/// Dedicated EUF (Equality with Uninterpreted Functions) decision procedure with congruence closure,
/// backtrackable union-find, and proof forest conflict generation.
public final class EUFSolver: TheorySolver, @unchecked Sendable {
    public let theoryId: TheoryId = .euf

    private var nodes: [ENode] = []
    private var termToNodeId: [Expr: Int] = [:]
    private var sigTable: [ENodeSignature: Int] = [:]

    // Union-find forest
    private var parent: [Int] = []
    private var rank: [Int] = []

    // Undirected proof graph for conflict explanations
    private var proofAdj: [Int: [(target: Int, reason: Expr)]] = [:]

    // Asserted disequalities: (nodeA, nodeB, originalExpr)
    private var disequalities: [(Int, Int, Expr)] = []

    // Scope undo trail for backtracking
    private struct UndoStep: Sendable {
        enum Kind {
            case union(rootPushed: Int, oldParent: Int, oldRank: Int)
            case addNode(nodeId: Int, term: Expr)
            case addSig(sig: ENodeSignature)
            case addParent(childNodeId: Int, parentNodeId: Int)
            case addDisequality
            case addProofEdge(a: Int, b: Int)
        }
        let kind: Kind
    }

    private var undoTrail: [UndoStep] = []
    private var scopeLimits: [Int] = []

    // Deductions discovered during congruence closure
    private var pendingDeductions: [TheoryDeduction] = []

    public init() {}

    // MARK: - Term Registration

    /// Register an expression and its subterms into the E-graph, returning its E-node ID.
    @discardableResult
    public func intern(term: Expr) -> Int {
        if let existing = termToNodeId[term] {
            return existing
        }

        let newId = nodes.count
        let node = ENode(id: newId, term: term)
        nodes.append(node)
        parent.append(newId)
        rank.append(0)
        termToNodeId[term] = newId
        undoTrail.append(UndoStep(kind: .addNode(nodeId: newId, term: term)))

        // Register subterms for function applications
        switch term {
        case let .apply(symbol, args, _):
            var argClassIds: [Int] = []
            for arg in args {
                let argId = intern(term: arg)
                let cId = find(argId)
                argClassIds.append(cId)
                nodes[cId].parents.append(newId)
                undoTrail.append(UndoStep(kind: .addParent(childNodeId: cId, parentNodeId: newId)))
            }
            let sig = ENodeSignature(symbol: symbol, argClasses: argClassIds)
            sigTable[sig] = newId
            undoTrail.append(UndoStep(kind: .addSig(sig: sig)))

        default:
            break
        }

        return newId
    }

    // MARK: - Union-Find with Proof Forest

    public func find(_ id: Int) -> Int {
        var curr = id
        while parent[curr] != curr {
            curr = parent[curr]
        }
        return curr
    }

    /// Merge two equivalence classes with an explicit justification expression.
    private func merge(nodeA: Int, nodeB: Int, reason: Expr) -> TheoryResult {
        let rootA = find(nodeA)
        let rootB = find(nodeB)
        if rootA == rootB {
            return .consistent
        }

        // Link smaller rank tree to larger rank tree
        let (newRoot, subRoot) = rank[rootA] < rank[rootB] ? (rootB, rootA) : (rootA, rootB)
        let oldRank = rank[newRoot]

        parent[subRoot] = newRoot
        if rank[rootA] == rank[rootB] {
            rank[newRoot] += 1
        }

        // Record proof edge for conflict explanations
        proofAdj[nodeA, default: []].append((nodeB, reason))
        proofAdj[nodeB, default: []].append((nodeA, reason))
        undoTrail.append(UndoStep(kind: .union(rootPushed: subRoot, oldParent: subRoot, oldRank: oldRank)))
        undoTrail.append(UndoStep(kind: .addProofEdge(a: nodeA, b: nodeB)))

        // Check if any asserted disequality is violated
        for (da, db, deqExpr) in disequalities {
            if find(da) == find(db) {
                let expl = explainEquivalence(da, db) + [deqExpr]
                return .conflict(explanation: expl)
            }
        }

        // Propagate congruences along parent applications
        let parentsA = nodes[rootA].parents
        let parentsB = nodes[rootB].parents

        for pA in parentsA {
            guard let sigA = signature(of: pA) else { continue }
            for pB in parentsB {
                guard pA != pB else { continue }
                guard let sigB = signature(of: pB) else { continue }
                if sigA == sigB {
                    // Congruence rule: f(x1..xn) == f(y1..yn) if x_i == y_i
                    let congReason = Expr.eq(nodes[pA].term, nodes[pB].term)
                    let res = merge(nodeA: pA, nodeB: pB, reason: congReason)
                    if case .conflict = res {
                        return res
                    }
                    pendingDeductions.append(TheoryDeduction(literal: congReason, explanation: explainEquivalence(pA, pB)))
                }
            }
        }

        return .consistent
    }

    private func signature(of nodeId: Int) -> ENodeSignature? {
        guard case let .apply(symbol, args, _) = nodes[nodeId].term else { return nil }
        var argClasses: [Int] = []
        for arg in args {
            guard let id = termToNodeId[arg] else { return nil }
            argClasses.append(find(id))
        }
        return ENodeSignature(symbol: symbol, argClasses: argClasses)
    }

    // MARK: - Explanations

    /// Trace shortest path between two nodes in the proof graph using BFS to find justifying equalities.
    public func explainEquivalence(_ start: Int, _ end: Int) -> [Expr] {
        if start == end { return [] }
        var visited = Set<Int>([start])
        var queue = [start]
        var parentEdge = [Int: (prev: Int, reason: Expr)]()

        while !queue.isEmpty {
            let u = queue.removeFirst()
            if u == end { break }
            for edge in proofAdj[u] ?? [] {
                if !visited.contains(edge.target) {
                    visited.insert(edge.target)
                    parentEdge[edge.target] = (u, edge.reason)
                    queue.append(edge.target)
                }
            }
        }

        var result: [Expr] = []
        var curr = end
        while let edge = parentEdge[curr] {
            result.append(edge.reason)
            curr = edge.prev
        }
        return result
    }

    // MARK: - TheorySolver Conformance

    public func pushScope() {
        scopeLimits.append(undoTrail.count)
    }

    public func popScope() {
        guard let limit = scopeLimits.popLast() else { return }
        while undoTrail.count > limit {
            let step = undoTrail.removeLast()
            switch step.kind {
            case let .union(rootPushed, oldParent, oldRank):
                parent[rootPushed] = oldParent
                rank[parent[rootPushed]] = oldRank
            case let .addProofEdge(a, b):
                if var listA = proofAdj[a], !listA.isEmpty {
                    listA.removeLast()
                    proofAdj[a] = listA
                }
                if var listB = proofAdj[b], !listB.isEmpty {
                    listB.removeLast()
                    proofAdj[b] = listB
                }
            case let .addNode(nodeId, term):
                termToNodeId.removeValue(forKey: term)
                if nodeId == nodes.count - 1 {
                    nodes.removeLast()
                    parent.removeLast()
                    rank.removeLast()
                }
            case let .addSig(sig):
                sigTable.removeValue(forKey: sig)
            case let .addParent(childId, parentId):
                if childId < nodes.count {
                    nodes[childId].parents.removeAll { $0 == parentId }
                }
            case .addDisequality:
                _ = disequalities.popLast()
            }
        }
    }

    public func reset() {
        nodes.removeAll(keepingCapacity: true)
        termToNodeId.removeAll(keepingCapacity: true)
        sigTable.removeAll(keepingCapacity: true)
        parent.removeAll(keepingCapacity: true)
        rank.removeAll(keepingCapacity: true)
        proofAdj.removeAll(keepingCapacity: true)
        disequalities.removeAll(keepingCapacity: true)
        undoTrail.removeAll(keepingCapacity: true)
        scopeLimits.removeAll(keepingCapacity: true)
        pendingDeductions.removeAll(keepingCapacity: true)
    }

    public func assertLiteral(_ literal: Expr) -> TheoryResult {
        switch literal {
        case let .eq(lhs, rhs):
            let idA = intern(term: lhs)
            let idB = intern(term: rhs)
            return merge(nodeA: idA, nodeB: idB, reason: literal)

        case let .not(inner):
            if case let .eq(lhs, rhs) = inner {
                let idA = intern(term: lhs)
                let idB = intern(term: rhs)
                if find(idA) == find(idB) {
                    // Immediate conflict: asserting a != b when a == b
                    let expl = explainEquivalence(idA, idB) + [literal]
                    return .conflict(explanation: expl)
                }
                disequalities.append((idA, idB, literal))
                undoTrail.append(UndoStep(kind: .addDisequality))
                return .consistent
            }
            return .consistent

        default:
            return .consistent
        }
    }

    public func checkConsistency() -> TheoryResult {
        for (da, db, deqExpr) in disequalities {
            if find(da) == find(db) {
                let expl = explainEquivalence(da, db) + [deqExpr]
                return .conflict(explanation: expl)
            }
        }
        return .consistent
    }

    public func propagateDeductions() -> [TheoryDeduction] {
        let deductions = pendingDeductions
        pendingDeductions.removeAll(keepingCapacity: true)
        return deductions
    }

    public func collectSharedTerms() -> [Expr] {
        return nodes.map { $0.term }
    }

    /// Check if two expressions are proven equivalent in the current E-graph.
    public func areEquivalent(_ a: Expr, _ b: Expr) -> Bool {
        guard let idA = termToNodeId[a], let idB = termToNodeId[b] else {
            return false
        }
        return find(idA) == find(idB)
    }
}
