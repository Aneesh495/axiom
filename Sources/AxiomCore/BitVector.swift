import Foundation
import CAxiomKernel

/// Fixed-size arbitrary-width bit-vector implementing exact SMT-LIB 2.6 QF_BV bit-vector semantics.
/// Supports bit widths from 1 to 4096+ bits with hardware SIMD acceleration.
public struct BitVector: Hashable, Comparable, CustomStringConvertible, Sendable {
    /// Bit width (must be >= 1)
    public let width: Int

    /// Packed 64-bit words stored in little-endian order
    public private(set) var words: [UInt64]

    // MARK: - Initializers

    public init(width: Int, value: UInt64 = 0) {
        precondition(width >= 1, "BitVector width must be at least 1")
        self.width = width
        let wordCount = (width + 63) / 64
        var w = [UInt64](repeating: 0, count: wordCount)
        if wordCount > 0 {
            w[0] = value
        }
        self.words = w
        self.maskTopWord()
    }

    public init(width: Int, words: [UInt64]) {
        precondition(width >= 1, "BitVector width must be at least 1")
        self.width = width
        let wordCount = (width + 63) / 64
        var w = words
        if w.count < wordCount {
            w.append(contentsOf: repeatElement(0, count: wordCount - w.count))
        } else if w.count > wordCount {
            w = Array(w.prefix(wordCount))
        }
        self.words = w
        self.maskTopWord()
    }

    public init(width: Int, bigInt: BigInt) {
        precondition(width >= 1, "BitVector width must be at least 1")
        self.width = width
        let wordCount = (width + 63) / 64
        var w = [UInt64](repeating: 0, count: wordCount)

        let mag = bigInt.magnitude
        for i in 0..<min(wordCount, mag.count) {
            w[i] = mag[i]
        }

        if bigInt.isNegative {
            // Two's complement negation: invert and add 1
            var carry: UInt64 = 1
            for i in 0..<wordCount {
                let inverted = ~w[i]
                let (sum, ov) = inverted.addingReportingOverflow(carry)
                w[i] = sum
                carry = ov ? 1 : 0
            }
        }

        self.words = w
        self.maskTopWord()
    }

    public init?(binaryString: String) {
        var str = binaryString.trimmingCharacters(in: .whitespacesAndNewlines)
        if str.hasPrefix("#b") {
            str.removeFirst(2)
        }
        if str.isEmpty { return nil }

        let width = str.count
        var words = [UInt64](repeating: 0, count: (width + 63) / 64)

        for (idx, char) in str.enumerated() {
            let bitPos = width - 1 - idx
            let wordIdx = bitPos / 64
            let bitOffset = bitPos % 64
            if char == "1" {
                words[wordIdx] |= (1 << bitOffset)
            } else if char != "0" {
                return nil
            }
        }

        self.width = width
        self.words = words
        self.maskTopWord()
    }

    public init?(hexString: String, width: Int? = nil) {
        var str = hexString.trimmingCharacters(in: .whitespacesAndNewlines)
        if str.hasPrefix("#x") {
            str.removeFirst(2)
        }
        if str.isEmpty { return nil }

        let targetWidth = width ?? (str.count * 4)
        guard targetWidth >= str.count * 4 - 3 else { return nil }

        var bv = BitVector(width: targetWidth, value: 0)
        for (idx, char) in str.enumerated() {
            guard let hexVal = char.hexDigitValue else { return nil }
            let hexPos = str.count - 1 - idx
            let bitStart = hexPos * 4
            for b in 0..<4 {
                let bit = (hexVal >> b) & 1
                if bit == 1 {
                    bv.setBit(at: bitStart + b, value: true)
                }
            }
        }
        self = bv
    }

    // MARK: - Masking Invariant

    private mutating func maskTopWord() {
        let remainder = width % 64
        if remainder != 0, let lastIdx = words.indices.last {
            let mask = (UInt64(1) << remainder) - 1
            words[lastIdx] &= mask
        }
    }

    // MARK: - Constants & Queries

    public static func zero(width: Int) -> BitVector {
        return BitVector(width: width, value: 0)
    }

    public static func ones(width: Int) -> BitVector {
        let wordCount = (width + 63) / 64
        let w = [UInt64](repeating: ~0, count: wordCount)
        var bv = BitVector(width: width, words: w)
        bv.maskTopWord()
        return bv
    }

    public var isZero: Bool {
        return words.withUnsafeBufferPointer { buf in
            axiom_vec_is_zero(buf.baseAddress, buf.count) != 0
        }
    }

    public var isAllOnes: Bool {
        return self == BitVector.ones(width: width)
    }

    public var msb: Bool {
        return getBit(at: width - 1)
    }

    public var lsb: Bool {
        return getBit(at: 0)
    }

    // MARK: - Bit Access

    public func getBit(at index: Int) -> Bool {
        precondition(index >= 0 && index < width, "Bit index out of bounds: \(index) for width \(width)")
        let wordIdx = index / 64
        let bitOffset = index % 64
        return ((words[wordIdx] >> bitOffset) & 1) == 1
    }

    public mutating func setBit(at index: Int, value: Bool) {
        precondition(index >= 0 && index < width, "Bit index out of bounds: \(index) for width \(width)")
        let wordIdx = index / 64
        let bitOffset = index % 64
        if value {
            words[wordIdx] |= (UInt64(1) << bitOffset)
        } else {
            words[wordIdx] &= ~(UInt64(1) << bitOffset)
        }
    }

    // MARK: - Bitwise Logic

    public static prefix func ~ (bv: BitVector) -> BitVector {
        var res = bv
        res.words.withUnsafeMutableBufferPointer { dst in
            bv.words.withUnsafeBufferPointer { src in
                axiom_vec_not(dst.baseAddress, src.baseAddress, src.count)
            }
        }
        res.maskTopWord()
        return res
    }

    public static func & (lhs: BitVector, rhs: BitVector) -> BitVector {
        precondition(lhs.width == rhs.width, "BitVector width mismatch: \(lhs.width) != \(rhs.width)")
        var res = lhs
        res.words.withUnsafeMutableBufferPointer { dst in
            lhs.words.withUnsafeBufferPointer { src1 in
                rhs.words.withUnsafeBufferPointer { src2 in
                    axiom_vec_and(dst.baseAddress, src1.baseAddress, src2.baseAddress, src1.count)
                }
            }
        }
        return res
    }

    public static func | (lhs: BitVector, rhs: BitVector) -> BitVector {
        precondition(lhs.width == rhs.width, "BitVector width mismatch: \(lhs.width) != \(rhs.width)")
        var res = lhs
        res.words.withUnsafeMutableBufferPointer { dst in
            lhs.words.withUnsafeBufferPointer { src1 in
                rhs.words.withUnsafeBufferPointer { src2 in
                    axiom_vec_or(dst.baseAddress, src1.baseAddress, src2.baseAddress, src1.count)
                }
            }
        }
        return res
    }

    public static func ^ (lhs: BitVector, rhs: BitVector) -> BitVector {
        precondition(lhs.width == rhs.width, "BitVector width mismatch: \(lhs.width) != \(rhs.width)")
        var res = lhs
        res.words.withUnsafeMutableBufferPointer { dst in
            lhs.words.withUnsafeBufferPointer { src1 in
                rhs.words.withUnsafeBufferPointer { src2 in
                    axiom_vec_xor(dst.baseAddress, src1.baseAddress, src2.baseAddress, src1.count)
                }
            }
        }
        return res
    }

    // MARK: - Shifts & Rotates

    public func shiftLeft(by amount: Int) -> BitVector {
        if amount <= 0 { return self }
        if amount >= width { return BitVector.zero(width: width) }

        var result = BitVector.zero(width: width)
        let wordShift = amount / 64
        let bitShift = amount % 64

        for i in 0..<words.count {
            let target = i + wordShift
            if target < words.count {
                result.words[target] |= words[i] << bitShift
            }
            if bitShift > 0 && (target + 1) < words.count {
                result.words[target + 1] |= words[i] >> (64 - bitShift)
            }
        }
        result.maskTopWord()
        return result
    }

    public func logicalShiftRight(by amount: Int) -> BitVector {
        if amount <= 0 { return self }
        if amount >= width { return BitVector.zero(width: width) }

        var result = BitVector.zero(width: width)
        let wordShift = amount / 64
        let bitShift = amount % 64

        for i in wordShift..<words.count {
            let target = i - wordShift
            result.words[target] |= words[i] >> bitShift
            if bitShift > 0 && (i + 1) < words.count {
                result.words[target] |= words[i + 1] << (64 - bitShift)
            }
        }
        result.maskTopWord()
        return result
    }

    public func arithmeticShiftRight(by amount: Int) -> BitVector {
        if amount <= 0 { return self }
        let signBit = self.msb

        if amount >= width {
            return signBit ? BitVector.ones(width: width) : BitVector.zero(width: width)
        }

        var result = logicalShiftRight(by: amount)
        if signBit {
            // Fill high bits with 1
            for b in (width - amount)..<width {
                result.setBit(at: b, value: true)
            }
        }
        return result
    }

    public func rotateLeft(by amount: Int) -> BitVector {
        let eff = amount % width
        if eff == 0 { return self }
        let left = shiftLeft(by: eff)
        let right = logicalShiftRight(by: width - eff)
        return left | right
    }

    public func rotateRight(by amount: Int) -> BitVector {
        let eff = amount % width
        if eff == 0 { return self }
        let right = logicalShiftRight(by: eff)
        let left = shiftLeft(by: width - eff)
        return left | right
    }

    // MARK: - Slicing & Extension

    public func extract(high: Int, low: Int) -> BitVector {
        precondition(high >= low && low >= 0 && high < width, "Invalid extract indices [\(high):\(low)] for width \(width)")
        let newWidth = high - low + 1
        var result = BitVector.zero(width: newWidth)

        for i in 0..<newWidth {
            if getBit(at: low + i) {
                result.setBit(at: i, value: true)
            }
        }
        return result
    }

    public static func concat(_ lhs: BitVector, _ rhs: BitVector) -> BitVector {
        let totalWidth = lhs.width + rhs.width
        var result = BitVector.zero(width: totalWidth)

        for i in 0..<rhs.width {
            if rhs.getBit(at: i) {
                result.setBit(at: i, value: true)
            }
        }
        for i in 0..<lhs.width {
            if lhs.getBit(at: i) {
                result.setBit(at: rhs.width + i, value: true)
            }
        }
        return result
    }

    public func zeroExtend(by count: Int) -> BitVector {
        precondition(count >= 0, "Extension count must be non-negative")
        if count == 0 { return self }
        let newWidth = width + count
        var result = BitVector(width: newWidth, words: self.words)
        result.maskTopWord()
        return result
    }

    public func signExtend(by count: Int) -> BitVector {
        precondition(count >= 0, "Extension count must be non-negative")
        if count == 0 { return self }
        let newWidth = width + count
        var result = zeroExtend(by: count)
        if msb {
            for b in width..<newWidth {
                result.setBit(at: b, value: true)
            }
        }
        return result
    }

    // MARK: - Arithmetic Modulo 2^w

    public static prefix func - (bv: BitVector) -> BitVector {
        return (~bv) + BitVector(width: bv.width, value: 1)
    }

    public static func + (lhs: BitVector, rhs: BitVector) -> BitVector {
        precondition(lhs.width == rhs.width, "BitVector width mismatch in addition")
        let count = lhs.words.count
        var result = [UInt64](repeating: 0, count: count)
        var carry: UInt64 = 0

        for i in 0..<count {
            let (sum1, ov1) = lhs.words[i].addingReportingOverflow(rhs.words[i])
            let (sum2, ov2) = sum1.addingReportingOverflow(carry)
            result[i] = sum2
            carry = (ov1 ? 1 : 0) + (ov2 ? 1 : 0)
        }

        var bv = BitVector(width: lhs.width, words: result)
        bv.maskTopWord()
        return bv
    }

    public static func - (lhs: BitVector, rhs: BitVector) -> BitVector {
        precondition(lhs.width == rhs.width, "BitVector width mismatch in subtraction")
        return lhs + (-rhs)
    }

    public static func * (lhs: BitVector, rhs: BitVector) -> BitVector {
        precondition(lhs.width == rhs.width, "BitVector width mismatch in multiplication")
        let count = lhs.words.count
        var result = [UInt64](repeating: 0, count: count)

        for i in 0..<count {
            let a = lhs.words[i]
            if a == 0 { continue }
            var carry: UInt64 = 0
            for j in 0..<(count - i) {
                let b = rhs.words[j]
                let (high, low) = a.multipliedFullWidth(by: b)
                let (s1, o1) = low.addingReportingOverflow(carry)
                let (s2, o2) = s1.addingReportingOverflow(result[i + j])
                result[i + j] = s2
                carry = high &+ (o1 ? 1 : 0) &+ (o2 ? 1 : 0)
            }
        }

        var bv = BitVector(width: lhs.width, words: result)
        bv.maskTopWord()
        return bv
    }

    public func unsignedDividingBy(_ rhs: BitVector) -> (quotient: BitVector, remainder: BitVector) {
        precondition(self.width == rhs.width, "BitVector width mismatch in division")
        precondition(!rhs.isZero, "Division by zero in BitVector unsigned division")

        let lhsBig = self.asUnsignedBigInt
        let rhsBig = rhs.asUnsignedBigInt
        let (qBig, rBig) = lhsBig.quotientAndRemainder(dividingBy: rhsBig)

        return (BitVector(width: self.width, bigInt: qBig), BitVector(width: self.width, bigInt: rBig))
    }

    public func signedDividingBy(_ rhs: BitVector) -> (quotient: BitVector, remainder: BitVector) {
        precondition(self.width == rhs.width, "BitVector width mismatch in division")
        precondition(!rhs.isZero, "Division by zero in BitVector signed division")

        let lhsBig = self.asSignedBigInt
        let rhsBig = rhs.asSignedBigInt
        let (qBig, rBig) = lhsBig.quotientAndRemainder(dividingBy: rhsBig)

        return (BitVector(width: self.width, bigInt: qBig), BitVector(width: self.width, bigInt: rBig))
    }

    // MARK: - Comparisons

    public static func < (lhs: BitVector, rhs: BitVector) -> Bool {
        return lhs.unsignedLessThan(rhs)
    }

    public func unsignedLessThan(_ rhs: BitVector) -> Bool {
        precondition(self.width == rhs.width, "BitVector width mismatch in comparison")
        for i in stride(from: words.count - 1, through: 0, by: -1) {
            if words[i] != rhs.words[i] {
                return words[i] < rhs.words[i]
            }
        }
        return false
    }

    public func signedLessThan(_ rhs: BitVector) -> Bool {
        precondition(self.width == rhs.width, "BitVector width mismatch in comparison")
        let lSign = self.msb
        let rSign = rhs.msb

        if lSign != rSign {
            return lSign // if lhs is negative (msb=1) and rhs is positive (msb=0), lhs < rhs
        }
        return self.unsignedLessThan(rhs)
    }

    // MARK: - Conversions & Representations

    public var asUnsignedBigInt: BigInt {
        return BigInt(sign: .plus, magnitude: self.words)
    }

    public var asSignedBigInt: BigInt {
        if !msb {
            return asUnsignedBigInt
        }
        // Negative: value = -((~self + 1))
        let negVal = (-self).asUnsignedBigInt
        return -negVal
    }

    public var asUInt64: UInt64? {
        if width > 64 { return nil }
        return words.first ?? 0
    }

    public var description: String {
        var str = "#b"
        for i in stride(from: width - 1, through: 0, by: -1) {
            str.append(getBit(at: i) ? "1" : "0")
        }
        return str
    }

    public var hexDescription: String {
        var str = "#x"
        let hexDigits = (width + 3) / 4
        for h in stride(from: hexDigits - 1, through: 0, by: -1) {
            var val: UInt64 = 0
            for b in 0..<4 {
                let bitIdx = h * 4 + b
                if bitIdx < width && getBit(at: bitIdx) {
                    val |= (1 << b)
                }
            }
            str.append(String(val, radix: 16))
        }
        return str
    }
}
