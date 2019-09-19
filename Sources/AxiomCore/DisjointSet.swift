import Foundation

/// Backtrackable Disjoint-Set (Union-Find) with rank-based union, undo trail,
/// and proof-forest edge labels for conflict explanation in congruence closure.
public final class DisjointSet: @unchecked Sendable {
    /// Structure recording modifications to restore previous states during backtracking
    private struct UndoEntry {
        let child: Int
        let oldParent: Int
        let parentOldRank: Int
        let reason: UInt32
    }

    /// Parent pointers: parent[i] == i implies i is the canonical representative
    private var parent: [Int]

    /// Rank (tree depth bound) for balanced union
    private var rank: [Int]

    /// Proof forest edge labels explaining why parent[i] was set
    private var edgeReason: [UInt32]

    /// Circular linked lists of equivalence class members for fast class traversal
    private var nextInClass: [Int]

    /// Undo stack for backtracking to previous decision levels
    private var undoStack: [UndoEntry]

    /// Checkpoint markers indexing into undoStack
    private var checkpoints: [Int]

    // MARK: - Initializer

    public init(capacity: Int = 128) {
        self.parent = []
        self.rank = []
        self.edgeReason = []
        self.nextInClass = []
        self.undoStack = []
        self.checkpoints = []

        self.parent.reserveCapacity(capacity)
        self.rank.reserveCapacity(capacity)
        self.edgeReason.reserveCapacity(capacity)
        self.nextInClass.reserveCapacity(capacity)
    }

    // MARK: - Element Creation

    @discardableResult
    public func makeSet() -> Int {
        let id = parent.count
        parent.append(id)
        rank.append(0)
        edgeReason.append(0)
        nextInClass.append(id)
        return id
    }

    public var count: Int {
        return parent.count
    }

    // MARK: - Find with Backtracking (No Path Compression during active trails)

    /// Finds the canonical representative of element i.
    /// Note: Path compression is omitted or logged to preserve exact backtracking and proof forest edges.
    public func find(_ i: Int) -> Int {
        precondition(i >= 0 && i < parent.count, "Index out of range: \(i)")
        var curr = i
        while parent[curr] != curr {
            curr = parent[curr]
        }
        return curr
    }

    public func areEquivalent(_ a: Int, _ b: Int) -> Bool {
        return find(a) == find(b)
    }

    // MARK: - Union with Backtracking and Proof Logging

    /// Merges the equivalence classes containing a and b.
    /// Returns true if a new merge occurred, or false if they were already equivalent.
    @discardableResult
    public func union(_ a: Int, _ b: Int, reason: UInt32 = 0) -> Bool {
        let rootA = find(a)
        let rootB = find(b)
        if rootA == rootB {
            return false
        }

        // Union by rank
        let child: Int
        let newParent: Int

        if rank[rootA] < rank[rootB] {
            child = rootA
            newParent = rootB
        } else if rank[rootA] > rank[rootB] {
            child = rootB
            newParent = rootA
        } else {
            child = rootB
            newParent = rootA
            // Increment rank of new parent
            rank[newParent] += 1
        }

        // Record undo entry
        undoStack.append(UndoEntry(
            child: child,
            oldParent: child,
            parentOldRank: rank[newParent],
            reason: edgeReason[child]
        ))

        // Update parent and edge label
        parent[child] = newParent
        edgeReason[child] = reason

        // Splice circular linked lists of class members
        let temp = nextInClass[child]
        nextInClass[child] = nextInClass[newParent]
        nextInClass[newParent] = temp

        return true
    }

    // MARK: - Proof Forest Edge Traversal

    /// Returns the path of proof reasons connecting a and b in the union-find forest.
    public func explainEquivalence(_ a: Int, _ b: Int) -> [UInt32] {
        precondition(areEquivalent(a, b), "Elements are not equivalent; cannot explain")
        let pathA = pathToRoot(a)
        let pathB = pathToRoot(b)

        // Find Lowest Common Ancestor (LCA)
        var lcaIndexA = pathA.count - 1
        var lcaIndexB = pathB.count - 1

        while lcaIndexA >= 0 && lcaIndexB >= 0 && pathA[lcaIndexA].node == pathB[lcaIndexB].node {
            lcaIndexA -= 1
            lcaIndexB -= 1
        }
        // Step back one to the actual LCA
        lcaIndexA += 1
        lcaIndexB += 1

        var reasons: [UInt32] = []
        for i in 0..<lcaIndexA {
            let r = pathA[i].reason
            if r != 0 { reasons.append(r) }
        }
        for i in 0..<lcaIndexB {
            let r = pathB[i].reason
            if r != 0 { reasons.append(r) }
        }
        return reasons
    }

    private func pathToRoot(_ start: Int) -> [(node: Int, reason: UInt32)] {
        var path: [(node: Int, reason: UInt32)] = []
        var curr = start
        while parent[curr] != curr {
            path.append((node: curr, reason: edgeReason[curr]))
            curr = parent[curr]
        }
        path.append((node: curr, reason: 0))
        return path
    }

    // MARK: - Class Members

    /// Returns all elements currently belonging to the same equivalence class as i.
    public func classMembers(of i: Int) -> [Int] {
        precondition(i >= 0 && i < parent.count, "Index out of range: \(i)")
        var members: [Int] = []
        var curr = i
        repeat {
            members.append(curr)
            curr = nextInClass[curr]
        } while curr != i
        return members
    }

    // MARK: - Checkpoints and Backtracking

    public func pushCheckpoint() -> Int {
        let token = checkpoints.count
        checkpoints.append(undoStack.count)
        return token
    }

    public func popCheckpoint(to token: Int) {
        precondition(token >= 0 && token < checkpoints.count, "Invalid checkpoint token: \(token)")
        let targetUndoIndex = checkpoints[token]
        checkpoints.removeSubrange(token...)

        while undoStack.count > targetUndoIndex {
            let entry = undoStack.removeLast()
            let child = entry.child
            let par = parent[child]

            // Restore circular linked list
            // Unsplice nextInClass
            let temp = nextInClass[child]
            nextInClass[child] = nextInClass[par]
            nextInClass[par] = temp

            parent[child] = entry.oldParent
            rank[par] = entry.parentOldRank
            edgeReason[child] = entry.reason
        }
    }

    public func reset() {
        undoStack.removeAll(keepingCapacity: true)
        checkpoints.removeAll(keepingCapacity: true)
        for i in 0..<parent.count {
            parent[i] = i
            rank[i] = 0
            edgeReason[i] = 0
            nextInClass[i] = i
        }
    }
}
