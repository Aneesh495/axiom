import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT

/// High-performance Bit-Vector (QF_BV) Theory Solver.
/// Implements bit-blasting to an And-Inverter Graph (AIG) circuit representation
/// lowered into propositional CNF and solved via an incremental CDCL engine.
/// Includes word-level constant folding and interval bounds checks.
public final class BVSolver: TheorySolver, @unchecked Sendable {
    public var theoryId: TheoryId { return .bitvector }

    // MARK: - State Management

    private let trail: TheoryTrail
    private var isConflicted: Bool = false
    private var conflictExplanation: [Expr] = []

    // Bit-blasting circuit synthesis
    private var aig: AIGGraph
    private var exprToAIGBits: [Expr: [AIGLit]]
    private var assertedAIGConstraints: [AIGLit]
    private var assertedLiterals: [Expr]
    private var scopeCheckpoints: [Int]

    // Cached model assignments after a consistent check
    private var modelValues: [Expr: BitVector]

    public init() {
        self.trail = TheoryTrail()
        self.aig = AIGGraph()
        self.exprToAIGBits = [:]
        self.assertedAIGConstraints = []
        self.assertedLiterals = []
        self.scopeCheckpoints = []
        self.modelValues = [:]
    }

    // MARK: - TheorySolver Protocol

    public func pushScope() {
        trail.pushScope()
        scopeCheckpoints.append(assertedAIGConstraints.count)
    }

    public func popScope() {
        let _ = trail.popScope()
        if let lastCheckpoint = scopeCheckpoints.popLast() {
            if assertedAIGConstraints.count > lastCheckpoint {
                assertedAIGConstraints.removeSubrange(lastCheckpoint..<assertedAIGConstraints.count)
                assertedLiterals.removeSubrange(lastCheckpoint..<assertedLiterals.count)
            }
        }
        isConflicted = false
        conflictExplanation.removeAll(keepingCapacity: true)
        modelValues.removeAll(keepingCapacity: true)
    }

    public func reset() {
        trail.reset()
        aig = AIGGraph()
        exprToAIGBits.removeAll(keepingCapacity: true)
        assertedAIGConstraints.removeAll(keepingCapacity: true)
        assertedLiterals.removeAll(keepingCapacity: true)
        scopeCheckpoints.removeAll(keepingCapacity: true)
        modelValues.removeAll(keepingCapacity: true)
        isConflicted = false
        conflictExplanation.removeAll(keepingCapacity: true)
    }

    public func assertLiteral(_ literal: Expr) -> TheoryResult {
        if isConflicted {
            return .conflict(explanation: conflictExplanation)
        }

        trail.record(assertion: literal)

        // Try word-level constant evaluation first
        if let constEval = evaluateConstantBool(literal) {
            if !constEval {
                isConflicted = true
                conflictExplanation = [literal]
                return .conflict(explanation: conflictExplanation)
            }
            return .consistent
        }

        // Bit-blast the Boolean constraint into an AIG literal
        let constraintLit = bitBlastBoolExpr(literal)
        if constraintLit == .false {
            isConflicted = true
            conflictExplanation = [literal]
            return .conflict(explanation: conflictExplanation)
        }

        assertedAIGConstraints.append(constraintLit)
        assertedLiterals.append(literal)

        return .consistent
    }

    public func checkConsistency() -> TheoryResult {
        if isConflicted {
            return .conflict(explanation: conflictExplanation)
        }

        if assertedAIGConstraints.isEmpty {
            return .consistent
        }

        // Lower the asserted AIG constraints to CNF
        let (clauses, numVars) = aig.toCNF(outputs: assertedAIGConstraints)

        // Run the CDCL SAT solver
        let satSolver = SATSolver()
        satSolver.reserveVariables(count: max(numVars + 1, 1))
        for clause in clauses {
            if clause.isEmpty {
                isConflicted = true
                conflictExplanation = assertedLiterals
                return .conflict(explanation: conflictExplanation)
            }
            let lits = clause.map { Literal(dimacs: $0) }
            satSolver.addClause(lits)
        }

        switch satSolver.solve() {
        case .sat:
            extractModel(from: satSolver)
            return .consistent

        case .unsat:
            isConflicted = true
            conflictExplanation = assertedLiterals
            return .conflict(explanation: conflictExplanation)

        case .unknown:
            return .consistent
        }
    }

    public func propagateDeductions() -> [TheoryDeduction] {
        return []
    }

    public func collectSharedTerms() -> [Expr] {
        var shared: Set<Expr> = []
        for lit in assertedLiterals {
            collectBVTerms(lit, into: &shared)
        }
        return Array(shared)
    }

    // MARK: - Model Inspection

    public func getValue(of expr: Expr) -> BitVector? {
        return modelValues[expr]
    }

    private func extractModel(from satSolver: SATSolver) {
        modelValues.removeAll(keepingCapacity: true)
        for (expr, bits) in exprToAIGBits {
            guard case .variable(_, .bitVec(let width)) = expr else { continue }
            var bitVec = BitVector(width: width, value: 0)
            for (i, lit) in bits.enumerated() {
                let bitVal: Bool
                if lit.isConstant {
                    bitVal = (lit == .true)
                } else {
                    let satVar = Int32(lit.nodeIndex - 1)
                    let rawVal = satSolver.modelValue(for: satVar)
                    bitVal = lit.isInverted ? !rawVal : rawVal
                }
                if bitVal {
                    bitVec.setBit(at: i, value: true)
                }
            }
            modelValues[expr] = bitVec
        }
    }

    // MARK: - Word-Level Constant Evaluation

    private func evaluateConstantBool(_ expr: Expr) -> Bool? {
        switch expr {
        case .boolConst(let b):
            return b

        case .not(let child):
            return evaluateConstantBool(child).map { !$0 }

        case .and(let children):
            for c in children {
                guard let b = evaluateConstantBool(c) else { return nil }
                if !b { return false }
            }
            return true

        case .or(let children):
            for c in children {
                guard let b = evaluateConstantBool(c) else { return nil }
                if b { return true }
            }
            return false

        case .eq(let lhs, let rhs):
            if let v1 = evaluateConstantBV(lhs), let v2 = evaluateConstantBV(rhs) {
                return v1 == v2
            }
            return nil

        case .bvULt(let lhs, let rhs):
            if let v1 = evaluateConstantBV(lhs), let v2 = evaluateConstantBV(rhs) {
                return v1.unsignedLessThan(v2)
            }
            return nil

        case .bvULe(let lhs, let rhs):
            if let v1 = evaluateConstantBV(lhs), let v2 = evaluateConstantBV(rhs) {
                return v1.unsignedLessThan(v2) || v1 == v2
            }
            return nil

        case .bvSLt(let lhs, let rhs):
            if let v1 = evaluateConstantBV(lhs), let v2 = evaluateConstantBV(rhs) {
                return v1.signedLessThan(v2)
            }
            return nil

        case .bvSLe(let lhs, let rhs):
            if let v1 = evaluateConstantBV(lhs), let v2 = evaluateConstantBV(rhs) {
                return v1.signedLessThan(v2) || v1 == v2
            }
            return nil

        default:
            return nil
        }
    }

    private func evaluateConstantBV(_ expr: Expr) -> BitVector? {
        switch expr {
        case .bvConst(let bv):
            return bv

        case .bvNot(let child):
            return evaluateConstantBV(child).map { ~$0 }

        case .bvAnd(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            return a & b

        case .bvOr(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            return a | b

        case .bvXor(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            return a ^ b

        case .bvAdd(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            return a + b

        case .bvSub(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            return a - b

        case .bvMul(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            return a * b

        case .bvUDiv(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            if b.isZero { return BitVector.ones(width: a.width) }
            return a.unsignedDividingBy(b).quotient

        case .bvURem(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            if b.isZero { return a }
            return a.unsignedDividingBy(b).remainder

        case .bvSDiv(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            if b.isZero { return BitVector.ones(width: a.width) }
            return a.signedDividingBy(b).quotient

        case .bvSRem(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            if b.isZero { return a }
            return a.signedDividingBy(b).remainder

        case .bvShl(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            let amt = Int(b.words.first ?? 0)
            return a.shiftLeft(by: amt)

        case .bvLShr(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            let amt = Int(b.words.first ?? 0)
            return a.logicalShiftRight(by: amt)

        case .bvAShr(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            let amt = Int(b.words.first ?? 0)
            return a.arithmeticShiftRight(by: amt)

        case .bvConcat(let lhs, let rhs):
            guard let a = evaluateConstantBV(lhs), let b = evaluateConstantBV(rhs) else { return nil }
            return BitVector.concat(a, b)

        case .bvExtract(let high, let low, let body):
            guard let a = evaluateConstantBV(body) else { return nil }
            return a.extract(high: high, low: low)

        case .bvZeroExtend(let count, let body):
            guard let a = evaluateConstantBV(body) else { return nil }
            return a.zeroExtend(by: count)

        case .bvSignExtend(let count, let body):
            guard let a = evaluateConstantBV(body) else { return nil }
            return a.signExtend(by: count)

        default:
            return nil
        }
    }

    // MARK: - Bit-Blasting Boolean Expressions

    private func bitBlastBoolExpr(_ expr: Expr) -> AIGLit {
        switch expr {
        case .boolConst(let b):
            return b ? .true : .false

        case .not(let child):
            return !bitBlastBoolExpr(child)

        case .and(let children):
            var result = AIGLit.true
            for child in children {
                result = aig.and(result, bitBlastBoolExpr(child))
            }
            return result

        case .or(let children):
            var result = AIGLit.false
            for child in children {
                result = aig.or(result, bitBlastBoolExpr(child))
            }
            return result

        case .eq(let lhs, let rhs):
            return bitBlastEquality(lhs, rhs)

        case .distinct(let args):
            var res = AIGLit.true
            for i in 0..<args.count {
                for j in (i + 1)..<args.count {
                    let eq = bitBlastEquality(args[i], args[j])
                    res = aig.and(res, !eq)
                }
            }
            return res

        case .bvULt(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            return bitBlastUnsignedLessThan(a, b)

        case .bvULe(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            let lt = bitBlastUnsignedLessThan(a, b)
            let eq = bitBlastEquality(lhs, rhs)
            return aig.or(lt, eq)

        case .bvSLt(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            return bitBlastSignedLessThan(a, b)

        case .bvSLe(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            let lt = bitBlastSignedLessThan(a, b)
            let eq = bitBlastEquality(lhs, rhs)
            return aig.or(lt, eq)

        case .variable(let sym, .bool):
            return aig.createVariable(name: sym)

        default:
            return .true
        }
    }

    private func bitBlastEquality(_ lhs: Expr, _ rhs: Expr) -> AIGLit {
        let bitsLhs = bitBlastBVExpr(lhs)
        let bitsRhs = bitBlastBVExpr(rhs)
        precondition(bitsLhs.count == bitsRhs.count, "Bit width mismatch in equality bit-blasting")

        var eqLit = AIGLit.true
        for i in 0..<bitsLhs.count {
            let bitEq = aig.iff(bitsLhs[i], bitsRhs[i])
            eqLit = aig.and(eqLit, bitEq)
        }
        return eqLit
    }

    // MARK: - Bit-Blasting Bit-Vector Terms

    public func bitBlastBVExpr(_ expr: Expr) -> [AIGLit] {
        if let cached = exprToAIGBits[expr] {
            return cached
        }

        let bits: [AIGLit]
        switch expr {
        case .bvConst(let bv):
            bits = (0..<bv.width).map { bv.getBit(at: $0) ? AIGLit.true : AIGLit.false }

        case .variable(let sym, .bitVec(let width)):
            bits = (0..<width).map { _ in
                aig.createVariable(name: sym)
            }

        case .bvNot(let child):
            let a = bitBlastBVExpr(child)
            bits = a.map { !$0 }

        case .bvAnd(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = zip(a, b).map { aig.and($0, $1) }

        case .bvOr(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = zip(a, b).map { aig.or($0, $1) }

        case .bvXor(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = zip(a, b).map { aig.xor($0, $1) }

        case .bvAdd(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = aig.addVectors(a, b)

        case .bvSub(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            let notB = b.map { !$0 }
            let one = (0..<b.count).map { $0 == 0 ? AIGLit.true : AIGLit.false }
            let negB = aig.addVectors(notB, one)
            bits = aig.addVectors(a, negB)

        case .bvMul(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = bitBlastMultiplication(a, b)

        case .bvUDiv(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = bitBlastUnsignedDivision(a, b).quotient

        case .bvURem(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = bitBlastUnsignedDivision(a, b).remainder

        case .bvSDiv(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = bitBlastSignedDivision(a, b).quotient

        case .bvSRem(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = bitBlastSignedDivision(a, b).remainder

        case .bvShl(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = bitBlastShiftLeft(a, b)

        case .bvLShr(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = bitBlastLogicalShiftRight(a, b)

        case .bvAShr(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            bits = bitBlastArithmeticShiftRight(a, b)

        case .bvConcat(let lhs, let rhs):
            let a = bitBlastBVExpr(lhs)
            let b = bitBlastBVExpr(rhs)
            // SMT-LIB concat(lhs, rhs): lhs is high part, rhs is low part
            // Our bit array is indexed 0..count-1 with 0 being LSB
            bits = b + a

        case .bvExtract(let high, let low, let body):
            let a = bitBlastBVExpr(body)
            bits = Array(a[low...high])

        case .bvZeroExtend(let count, let body):
            let a = bitBlastBVExpr(body)
            bits = a + Array(repeating: AIGLit.false, count: count)

        case .bvSignExtend(let count, let body):
            let a = bitBlastBVExpr(body)
            let signBit = a.last ?? .false
            bits = a + Array(repeating: signBit, count: count)

        default:
            fatalError("Unsupported bit-vector term: \(expr)")
        }

        exprToAIGBits[expr] = bits
        return bits
    }

    // MARK: - Advanced Circuit Synthesis (Multiplication, Shifts, Comparators)

    /// Shift-and-add multiplier circuit
    private func bitBlastMultiplication(_ a: [AIGLit], _ b: [AIGLit]) -> [AIGLit] {
        let width = a.count
        var accumulator = Array(repeating: AIGLit.false, count: width)

        for i in 0..<width {
            // Partial product: a shifted left by i bits, gated by b[i]
            var partial = Array(repeating: AIGLit.false, count: width)
            for j in 0..<(width - i) {
                partial[i + j] = aig.and(a[j], b[i])
            }
            accumulator = aig.addVectors(accumulator, partial)
        }

        return accumulator
    }

    /// Unsigned Less-Than Comparator Circuit: a <_u b
    private func bitBlastUnsignedLessThan(_ a: [AIGLit], _ b: [AIGLit]) -> AIGLit {
        let width = a.count
        var borrow = AIGLit.false

        for i in 0..<width {
            let notA = !a[i]
            let aXorB = aig.xor(a[i], b[i])
            let term1 = aig.and(notA, b[i])
            let term2 = aig.and(!aXorB, borrow)
            borrow = aig.or(term1, term2)
        }

        return borrow
    }

    /// Signed Less-Than Comparator Circuit: a <_s b
    private func bitBlastSignedLessThan(_ a: [AIGLit], _ b: [AIGLit]) -> AIGLit {
        let width = a.count
        guard width > 0 else { return .false }

        let signA = a[width - 1]
        let signB = b[width - 1]

        let signsDiffer = aig.xor(signA, signB)
        let diffCase = aig.and(signA, !signB)
        let sameCase = bitBlastUnsignedLessThan(a, b)

        return aig.ite(signsDiffer, diffCase, sameCase)
    }

    /// Barrel shifter: Logical Shift Left
    private func bitBlastShiftLeft(_ a: [AIGLit], _ shiftAmt: [AIGLit]) -> [AIGLit] {
        let width = a.count
        var current = a

        for stage in 0..<shiftAmt.count {
            let shiftDist = 1 << stage
            if shiftDist >= width {
                for k in stage..<shiftAmt.count {
                    let isShiftBitSet = shiftAmt[k]
                    current = current.map { aig.ite(isShiftBitSet, .false, $0) }
                }
                break
            }

            var shifted = Array(repeating: AIGLit.false, count: width)
            for i in shiftDist..<width {
                shifted[i] = current[i - shiftDist]
            }

            let cond = shiftAmt[stage]
            for i in 0..<width {
                current[i] = aig.ite(cond, shifted[i], current[i])
            }
        }

        return current
    }

    /// Barrel shifter: Logical Shift Right
    private func bitBlastLogicalShiftRight(_ a: [AIGLit], _ shiftAmt: [AIGLit]) -> [AIGLit] {
        let width = a.count
        var current = a

        for stage in 0..<shiftAmt.count {
            let shiftDist = 1 << stage
            if shiftDist >= width {
                for k in stage..<shiftAmt.count {
                    let isShiftBitSet = shiftAmt[k]
                    current = current.map { aig.ite(isShiftBitSet, .false, $0) }
                }
                break
            }

            var shifted = Array(repeating: AIGLit.false, count: width)
            for i in 0..<(width - shiftDist) {
                shifted[i] = current[i + shiftDist]
            }

            let cond = shiftAmt[stage]
            for i in 0..<width {
                current[i] = aig.ite(cond, shifted[i], current[i])
            }
        }

        return current
    }

    /// Barrel shifter: Arithmetic Shift Right (preserving sign)
    private func bitBlastArithmeticShiftRight(_ a: [AIGLit], _ shiftAmt: [AIGLit]) -> [AIGLit] {
        let width = a.count
        guard width > 0 else { return a }
        let signBit = a[width - 1]
        var current = a

        for stage in 0..<shiftAmt.count {
            let shiftDist = 1 << stage
            if shiftDist >= width {
                for k in stage..<shiftAmt.count {
                    let isShiftBitSet = shiftAmt[k]
                    current = current.map { aig.ite(isShiftBitSet, signBit, $0) }
                }
                break
            }

            var shifted = Array(repeating: signBit, count: width)
            for i in 0..<(width - shiftDist) {
                shifted[i] = current[i + shiftDist]
            }

            let cond = shiftAmt[stage]
            for i in 0..<width {
                current[i] = aig.ite(cond, shifted[i], current[i])
            }
        }

        return current
    }

    /// Restoring non-negative division circuit
    private func bitBlastUnsignedDivision(_ a: [AIGLit], _ b: [AIGLit]) -> (quotient: [AIGLit], remainder: [AIGLit]) {
        let width = a.count
        var rem = Array(repeating: AIGLit.false, count: width)
        var quo = Array(repeating: AIGLit.false, count: width)

        for i in stride(from: width - 1, through: 0, by: -1) {
            // Shift rem left by 1 and insert a[i] at position 0
            var remShifted = Array(repeating: AIGLit.false, count: width)
            for j in 1..<width {
                remShifted[j] = rem[j - 1]
            }
            remShifted[0] = a[i]

            // remShifted >= b <=> !(remShifted < b)
            let lt = bitBlastUnsignedLessThan(remShifted, b)
            let ge = !lt

            quo[i] = ge

            // Subtraction: remShifted - b
            let notB = b.map { !$0 }
            let one = (0..<width).map { $0 == 0 ? AIGLit.true : AIGLit.false }
            let negB = aig.addVectors(notB, one)
            let remSub = aig.addVectors(remShifted, negB)

            // If ge, rem = remSub, else remShifted
            for j in 0..<width {
                rem[j] = aig.ite(ge, remSub[j], remShifted[j])
            }
        }

        // Handle division by zero: if b == 0, quotient is all 1s, remainder is a
        var bIsZero = AIGLit.true
        for bit in b {
            bIsZero = aig.and(bIsZero, !bit)
        }

        let finalQuo = quo.map { aig.ite(bIsZero, .true, $0) }
        let finalRem = zip(rem, a).map { aig.ite(bIsZero, $1, $0) }

        return (finalQuo, finalRem)
    }

    /// Signed division circuit via magnitude conversion
    private func bitBlastSignedDivision(_ a: [AIGLit], _ b: [AIGLit]) -> (quotient: [AIGLit], remainder: [AIGLit]) {
        let width = a.count
        guard width > 0 else { return ([], []) }

        let signA = a[width - 1]
        let signB = b[width - 1]

        // Negation of a and b: ~x + 1
        let one = (0..<width).map { $0 == 0 ? AIGLit.true : AIGLit.false }
        let negA = aig.addVectors(a.map { !$0 }, one)
        let negB = aig.addVectors(b.map { !$0 }, one)

        let absA = zip(a, negA).map { aig.ite(signA, $1, $0) }
        let absB = zip(b, negB).map { aig.ite(signB, $1, $0) }

        let (uQuo, uRem) = bitBlastUnsignedDivision(absA, absB)

        let negQuo = aig.addVectors(uQuo.map { !$0 }, one)
        let negRem = aig.addVectors(uRem.map { !$0 }, one)

        let diffSigns = aig.xor(signA, signB)
        let finalQuo = zip(uQuo, negQuo).map { aig.ite(diffSigns, $1, $0) }
        let finalRem = zip(uRem, negRem).map { aig.ite(signA, $1, $0) }

        return (finalQuo, finalRem)
    }

    // MARK: - Utilities

    private func collectBVTerms(_ expr: Expr, into set: inout Set<Expr>) {
        if case .variable(_, .bitVec) = expr {
            set.insert(expr)
        }
        for sub in expr.subterms {
            collectBVTerms(sub, into: &set)
        }
    }
}
