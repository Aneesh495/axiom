import Foundation
import AxiomCore

/// Algebraic term simplifier and constant folder applying equisatisfiable rewrite rules
/// to normalize formulas and eliminate redundancies prior to SAT and theory solving.
public struct TermSimplifier: Sendable {
    public init() {}

    /// Recursively simplify an expression to a canonical simplified normal form
    public func simplify(_ expr: Expr) -> Expr {
        switch expr {
        // MARK: - Constants & Variables
        case .boolConst, .intConst, .realConst, .bvConst, .stringConst, .variable:
            return expr

        // MARK: - Propositional Logic
        case let .not(inner):
            let s = simplify(inner)
            if case let .boolConst(b) = s {
                return .boolConst(!b)
            }
            if case let .not(doubleNeg) = s {
                return doubleNeg
            }
            return .not(s)

        case let .and(args):
            var flattened: [Expr] = []
            var seen = Set<Expr>()

            for arg in args {
                let s = simplify(arg)
                if case let .boolConst(b) = s {
                    if !b { return .false } // False in AND absorbs the whole formula
                    continue // True in AND is redundant
                }
                if case let .and(nested) = s {
                    for n in nested {
                        if !seen.contains(n) {
                            seen.insert(n)
                            flattened.append(n)
                        }
                    }
                } else if !seen.contains(s) {
                    // Check for complementary literal x and not(x)
                    if seen.contains(.not(s)) || (isNegated(s) && seen.contains(negate(s))) {
                        return .false
                    }
                    seen.insert(s)
                    flattened.append(s)
                }
            }

            if flattened.isEmpty { return .true }
            if flattened.count == 1 { return flattened[0] }
            return .and(flattened)

        case let .or(args):
            var flattened: [Expr] = []
            var seen = Set<Expr>()

            for arg in args {
                let s = simplify(arg)
                if case let .boolConst(b) = s {
                    if b { return .true } // True in OR absorbs the whole formula
                    continue // False in OR is redundant
                }
                if case let .or(nested) = s {
                    for n in nested {
                        if !seen.contains(n) {
                            seen.insert(n)
                            flattened.append(n)
                        }
                    }
                } else if !seen.contains(s) {
                    // Check for complementary literal x and not(x)
                    if seen.contains(.not(s)) || (isNegated(s) && seen.contains(negate(s))) {
                        return .true
                    }
                    seen.insert(s)
                    flattened.append(s)
                }
            }

            if flattened.isEmpty { return .false }
            if flattened.count == 1 { return flattened[0] }
            return .or(flattened)

        case let .implies(lhs, rhs):
            let sLhs = simplify(lhs)
            let sRhs = simplify(rhs)
            if case let .boolConst(bLhs) = sLhs {
                return bLhs ? sRhs : .true
            }
            if case let .boolConst(bRhs) = sRhs {
                return bRhs ? .true : simplify(.not(sLhs))
            }
            if sLhs == sRhs { return .true }
            return simplify(.or([.not(sLhs), sRhs]))

        case let .xor(lhs, rhs):
            let sLhs = simplify(lhs)
            let sRhs = simplify(rhs)
            if case let .boolConst(bL) = sLhs {
                return bL ? simplify(.not(sRhs)) : sRhs
            }
            if case let .boolConst(bR) = sRhs {
                return bR ? simplify(.not(sLhs)) : sLhs
            }
            if sLhs == sRhs { return .false }
            return .xor(sLhs, sRhs)

        case let .iff(lhs, rhs):
            let sLhs = simplify(lhs)
            let sRhs = simplify(rhs)
            if sLhs == sRhs { return .true }
            if case let .boolConst(bL) = sLhs {
                return bL ? sRhs : simplify(.not(sRhs))
            }
            if case let .boolConst(bR) = sRhs {
                return bR ? sLhs : simplify(.not(sLhs))
            }
            return .eq(sLhs, sRhs)

        case let .ite(cond, thenB, elseB):
            let sCond = simplify(cond)
            let sThen = simplify(thenB)
            let sElse = simplify(elseB)

            if case let .boolConst(b) = sCond {
                return b ? sThen : sElse
            }
            if sThen == sElse { return sThen }
            return .ite(condition: sCond, thenBranch: sThen, elseBranch: sElse)

        // MARK: - Equality & Relations
        case let .eq(lhs, rhs):
            let sLhs = simplify(lhs)
            let sRhs = simplify(rhs)
            if sLhs == sRhs { return .true }

            // Constant vs Constant inequality
            switch (sLhs, sRhs) {
            case let (.boolConst(b1), .boolConst(b2)):
                return .boolConst(b1 == b2)
            case let (.intConst(i1), .intConst(i2)):
                return .boolConst(i1 == i2)
            case let (.realConst(r1), .realConst(r2)):
                return .boolConst(r1 == r2)
            case let (.bvConst(v1), .bvConst(v2)):
                return .boolConst(v1 == v2)
            default:
                return .eq(sLhs, sRhs)
            }

        case let .distinct(args):
            let sArgs = args.map { simplify($0) }
            // Check for duplicate constants
            var constants = Set<Expr>()
            for arg in sArgs {
                if isConstant(arg) {
                    if constants.contains(arg) {
                        return .false
                    }
                    constants.insert(arg)
                }
            }
            return .distinct(sArgs)

        // MARK: - Arithmetic Simplifications
        case let .add(args):
            var constInt = BigInt.zero
            var constReal = Rational.zero
            var isReal = false
            var nonConsts: [Expr] = []

            for arg in args {
                let s = simplify(arg)
                switch s {
                case let .intConst(i):
                    constInt = constInt + i
                case let .realConst(r):
                    isReal = true
                    constReal = constReal + r
                case let .add(nested):
                    nonConsts.append(contentsOf: nested)
                default:
                    nonConsts.append(s)
                }
            }

            if isReal {
                constReal = constReal + Rational(constInt)
                if nonConsts.isEmpty { return .realConst(constReal) }
                if !constReal.isZero { nonConsts.append(.realConst(constReal)) }
            } else {
                if nonConsts.isEmpty { return .intConst(constInt) }
                if !constInt.isZero { nonConsts.append(.intConst(constInt)) }
            }

            if nonConsts.isEmpty { return isReal ? .real(0) : .int(0) }
            if nonConsts.count == 1 { return nonConsts[0] }
            return .add(nonConsts)

        case let .sub(lhs, rhs):
            let sLhs = simplify(lhs)
            let sRhs = simplify(rhs)
            if sLhs == sRhs {
                return sLhs.sort.isReal ? .real(0) : .int(0)
            }
            switch (sLhs, sRhs) {
            case let (.intConst(i1), .intConst(i2)):
                return .intConst(i1 - i2)
            case let (.realConst(r1), .realConst(r2)):
                return .realConst(r1 - r2)
            default:
                return .sub(sLhs, sRhs)
            }

        case let .mul(args):
            var constInt = BigInt.one
            var constReal = Rational.one
            var isReal = false
            var nonConsts: [Expr] = []

            for arg in args {
                let s = simplify(arg)
                switch s {
                case let .intConst(i):
                    if i.isZero { return .int(0) }
                    constInt = constInt * i
                case let .realConst(r):
                    if r.isZero { return .real(0) }
                    isReal = true
                    constReal = constReal * r
                case let .mul(nested):
                    nonConsts.append(contentsOf: nested)
                default:
                    nonConsts.append(s)
                }
            }

            if isReal {
                constReal = constReal * Rational(constInt)
                if nonConsts.isEmpty { return .realConst(constReal) }
                if constReal != Rational.one { nonConsts.insert(.realConst(constReal), at: 0) }
            } else {
                if nonConsts.isEmpty { return .intConst(constInt) }
                if constInt != BigInt.one { nonConsts.insert(.intConst(constInt), at: 0) }
            }

            if nonConsts.isEmpty { return isReal ? .real(1) : .int(1) }
            if nonConsts.count == 1 { return nonConsts[0] }
            return .mul(nonConsts)

        // MARK: - Comparisons
        case let .lt(lhs, rhs):
            let sLhs = simplify(lhs)
            let sRhs = simplify(rhs)
            switch (sLhs, sRhs) {
            case let (.intConst(i1), .intConst(i2)):
                return .boolConst(i1 < i2)
            case let (.realConst(r1), .realConst(r2)):
                return .boolConst(r1 < r2)
            default:
                if sLhs == sRhs { return .false }
                return .lt(sLhs, sRhs)
            }

        case let .le(lhs, rhs):
            let sLhs = simplify(lhs)
            let sRhs = simplify(rhs)
            switch (sLhs, sRhs) {
            case let (.intConst(i1), .intConst(i2)):
                return .boolConst(i1 <= i2)
            case let (.realConst(r1), .realConst(r2)):
                return .boolConst(r1 <= r2)
            default:
                if sLhs == sRhs { return .true }
                return .le(sLhs, sRhs)
            }

        case let .gt(lhs, rhs):
            return simplify(.lt(rhs, lhs))

        case let .ge(lhs, rhs):
            return simplify(.le(rhs, lhs))

        // MARK: - Bit-Vector Simplifications
        case let .bvAdd(lhs, rhs):
            let sL = simplify(lhs)
            let sR = simplify(rhs)
            if case let (.bvConst(v1), .bvConst(v2)) = (sL, sR) {
                return .bvConst(v1 + v2)
            }
            if case let .bvConst(v) = sR, v.isZero { return sL }
            if case let .bvConst(v) = sL, v.isZero { return sR }
            return .bvAdd(sL, sR)

        case let .bvSub(lhs, rhs):
            let sL = simplify(lhs)
            let sR = simplify(rhs)
            if sL == sR {
                let w = sL.sort.bitVectorWidth ?? 32
                return .bv(width: w, value: 0)
            }
            if case let (.bvConst(v1), .bvConst(v2)) = (sL, sR) {
                return .bvConst(v1 - v2)
            }
            if case let .bvConst(v) = sR, v.isZero { return sL }
            return .bvSub(sL, sR)

        case let .bvAnd(lhs, rhs):
            let sL = simplify(lhs)
            let sR = simplify(rhs)
            if sL == sR { return sL }
            if case let (.bvConst(v1), .bvConst(v2)) = (sL, sR) {
                return .bvConst(v1 & v2)
            }
            if case let .bvConst(v) = sR {
                if v.isZero { return sR }
                if v.isAllOnes { return sL }
            }
            if case let .bvConst(v) = sL {
                if v.isZero { return sL }
                if v.isAllOnes { return sR }
            }
            return .bvAnd(sL, sR)

        case let .bvOr(lhs, rhs):
            let sL = simplify(lhs)
            let sR = simplify(rhs)
            if sL == sR { return sL }
            if case let (.bvConst(v1), .bvConst(v2)) = (sL, sR) {
                return .bvConst(v1 | v2)
            }
            if case let .bvConst(v) = sR {
                if v.isAllOnes { return sR }
                if v.isZero { return sL }
            }
            if case let .bvConst(v) = sL {
                if v.isAllOnes { return sL }
                if v.isZero { return sR }
            }
            return .bvOr(sL, sR)

        case let .bvXor(lhs, rhs):
            let sL = simplify(lhs)
            let sR = simplify(rhs)
            if sL == sR {
                let w = sL.sort.bitVectorWidth ?? 32
                return .bv(width: w, value: 0)
            }
            if case let (.bvConst(v1), .bvConst(v2)) = (sL, sR) {
                return .bvConst(v1 ^ v2)
            }
            if case let .bvConst(v) = sR, v.isZero { return sL }
            if case let .bvConst(v) = sL, v.isZero { return sR }
            return .bvXor(sL, sR)

        case let .bvExtract(high, low, body):
            let sBody = simplify(body)
            if case let .bvConst(v) = sBody {
                return .bvConst(v.extract(high: high, low: low))
            }
            if low == 0, let w = sBody.sort.bitVectorWidth, high == w - 1 {
                return sBody
            }
            return .bvExtract(high: high, low: low, body: sBody)

        case let .bvConcat(lhs, rhs):
            let sL = simplify(lhs)
            let sR = simplify(rhs)
            if case let (.bvConst(v1), .bvConst(v2)) = (sL, sR) {
                return .bvConst(BitVector.concat(v1, v2))
            }
            return .bvConcat(sL, sR)

        // MARK: - Array Simplifications
        case let .select(array, index):
            let sArr = simplify(array)
            let sIdx = simplify(index)
            if case let .store(_, innerIdx, innerVal) = sArr {
                if sIdx == innerIdx {
                    return innerVal // select(store(a, i, v), i) -> v
                }
            }
            if case let .constArray(_, val) = sArr {
                return val // select(constArray(v), i) -> v
            }
            return .select(array: sArr, index: sIdx)

        case let .store(array, index, value):
            let sArr = simplify(array)
            let sIdx = simplify(index)
            let sVal = simplify(value)
            if case let .select(innerArr, innerIdx) = sVal, innerArr == sArr && innerIdx == sIdx {
                return sArr // store(a, i, select(a, i)) -> a
            }
            return .store(array: sArr, index: sIdx, value: sVal)

        // MARK: - Fallback
        default:
            return expr
        }
    }

    private func isConstant(_ expr: Expr) -> Bool {
        switch expr {
        case .boolConst, .intConst, .realConst, .bvConst, .stringConst:
            return true
        default:
            return false
        }
    }

    private func isNegated(_ expr: Expr) -> Bool {
        if case .not = expr { return true }
        return false
    }

    private func negate(_ expr: Expr) -> Expr {
        if case let .not(inner) = expr { return inner }
        return .not(expr)
    }
}
