import Foundation
import AxiomCore
import CAxiomKernel

/// Compact And-Inverter Graph (AIG) literal where bit 0 is the inversion flag and bits 1..31 index the node.
public struct AIGLit: Hashable, Equatable, Comparable, CustomStringConvertible, Sendable {
    public let rawValue: UInt32

    @inline(__always)
    public init(rawValue: UInt32) {
        self.rawValue = rawValue
    }

    @inline(__always)
    public init(node: UInt32, isInverted: Bool) {
        self.rawValue = (node << 1) | (isInverted ? 1 : 0)
    }

    public static let `false` = AIGLit(rawValue: 0)
    public static let `true` = AIGLit(rawValue: 1)

    public var isConstant: Bool {
        return rawValue <= 1
    }

    public var isInverted: Bool {
        return (rawValue & 1) == 1
    }

    public var nodeIndex: UInt32 {
        return rawValue >> 1
    }

    @inline(__always)
    public static prefix func ! (lit: AIGLit) -> AIGLit {
        return AIGLit(rawValue: lit.rawValue ^ 1)
    }

    public static func < (lhs: AIGLit, rhs: AIGLit) -> Bool {
        return lhs.rawValue < rhs.rawValue
    }

    public var description: String {
        if self == .false { return "false" }
        if self == .true { return "true" }
        return (isInverted ? "~n" : "n") + "\(nodeIndex)"
    }
}

/// AIG internal two-input AND node
public struct AIGNode: Hashable, Sendable {
    public let left: AIGLit
    public let right: AIGLit

    public init(left: AIGLit, right: AIGLit) {
        // Enforce canonical ordering left <= right
        if left.rawValue <= right.rawValue {
            self.left = left
            self.right = right
        } else {
            self.left = right
            self.right = left
        }
    }
}

/// Research-grade And-Inverter Graph (AIG) circuit synthesizer with structural hashing (strashing)
/// and CNF lowering for bit-vector bit-blasting.
public final class AIGGraph: @unchecked Sendable {
    private var nodes: [AIGNode]
    private var strashTable: [AIGNode: UInt32]
    private var variableNames: [UInt32: Symbol]

    public init() {
        self.nodes = []
        self.strashTable = [:]
        self.variableNames = [:]
    }

    // MARK: - Variables and Constants

    public func createVariable(name: Symbol) -> AIGLit {
        let nodeIdx = UInt32(nodes.count + 1)
        nodes.append(AIGNode(left: .false, right: .false)) // variable placeholder
        variableNames[nodeIdx] = name
        return AIGLit(node: nodeIdx, isInverted: false)
    }

    // MARK: - Two-Level Structural Hashing AND Gate

    public func and(_ litA: AIGLit, _ litB: AIGLit) -> AIGLit {
        // Trivial algebraic simplifications
        if litA == .false || litB == .false { return .false }
        if litA == .true { return litB }
        if litB == .true { return litA }
        if litA == litB { return litA }
        if litA == !litB { return .false }

        let candidate = AIGNode(left: litA, right: litB)

        // Structural hash lookup
        if let existingNode = strashTable[candidate] {
            return AIGLit(node: existingNode, isInverted: false)
        }

        let newIndex = UInt32(nodes.count + 1)
        nodes.append(candidate)
        strashTable[candidate] = newIndex
        return AIGLit(node: newIndex, isInverted: false)
    }

    // MARK: - Derived Logic Gates

    public func or(_ litA: AIGLit, _ litB: AIGLit) -> AIGLit {
        // De Morgan: A or B = not(not A and not B)
        return !and(!litA, !litB)
    }

    public func xor(_ litA: AIGLit, _ litB: AIGLit) -> AIGLit {
        // A xor B = (A or B) and (not A or not B)
        return and(or(litA, litB), or(!litA, !litB))
    }

    public func ite(_ cond: AIGLit, _ thenLit: AIGLit, _ elseLit: AIGLit) -> AIGLit {
        // ite(C, T, E) = (C and T) or (not C and E)
        return or(and(cond, thenLit), and(!cond, elseLit))
    }

    public func iff(_ litA: AIGLit, _ litB: AIGLit) -> AIGLit {
        return !xor(litA, litB)
    }

    // MARK: - Arithmetic Bit-Blasting Primitives

    /// 1-bit Full Adder: returns (sum, carryOut)
    public func fullAdder(bitA: AIGLit, bitB: AIGLit, carryIn: AIGLit) -> (sum: AIGLit, carryOut: AIGLit) {
        let sum = xor(xor(bitA, bitB), carryIn)
        let carryOut = or(and(bitA, bitB), and(xor(bitA, bitB), carryIn))
        return (sum, carryOut)
    }

    /// Ripple-carry addition of two n-bit vectors
    public func addVectors(_ a: [AIGLit], _ b: [AIGLit]) -> [AIGLit] {
        precondition(a.count == b.count, "Vector bit width mismatch")
        var result: [AIGLit] = []
        var carry = AIGLit.false

        for i in 0..<a.count {
            let (s, c) = fullAdder(bitA: a[i], bitB: b[i], carryIn: carry)
            result.append(s)
            carry = c
        }
        return result
    }

    // MARK: - CNF Lowering

    /// Lowers the entire AIG reachable from the output literals into CNF clauses
    public func toCNF(outputs: [AIGLit]) -> (clauses: [[Int32]], numVars: Int) {
        var clauses: [[Int32]] = []
        var visited = Set<UInt32>()

        func cnfLit(_ lit: AIGLit) -> Int32 {
            let varIdx = Int32(lit.nodeIndex)
            return lit.isInverted ? -varIdx : varIdx
        }

        func visit(nodeIndex: UInt32) {
            guard nodeIndex > 0 && nodeIndex <= nodes.count else { return }
            guard !visited.contains(nodeIndex) else { return }
            visited.insert(nodeIndex)

            let node = nodes[Int(nodeIndex - 1)]
            // If it is an internal AND gate (not a primary input variable)
            if node.left != .false || node.right != .false {
                visit(nodeIndex: node.left.nodeIndex)
                visit(nodeIndex: node.right.nodeIndex)

                let w = Int32(nodeIndex)
                let u = cnfLit(node.left)
                let v = cnfLit(node.right)

                // w <=> (u and v) encoded as:
                // (~w or u), (~w or v), (w or ~u or ~v)
                clauses.append([-w, u])
                clauses.append([-w, v])
                clauses.append([w, -u, -v])
            }
        }

        for out in outputs {
            visit(nodeIndex: out.nodeIndex)
            if out == .true {
                // Trivial tautology
            } else if out == .false {
                // Unsatisfiable empty clause
                clauses.append([])
            } else {
                clauses.append([cnfLit(out)])
            }
        }

        return (clauses, nodes.count)
    }

    public var nodeCount: Int {
        return nodes.count
    }
}
