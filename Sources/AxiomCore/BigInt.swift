import Foundation

/// Arbitrary-precision signed integer implementing exact arithmetic,
/// schoolbook and Karatsuba multiplication, division, and bitwise logic.
public struct BigInt: Comparable, Hashable, CustomStringConvertible, ExpressibleByIntegerLiteral, Sendable {
    public enum Sign: Int8, Sendable {
        case plus = 1
        case minus = -1
    }

    /// Sign of the integer
    public var sign: Sign

    /// Magnitude stored as little-endian 64-bit words (limbs)
    public var magnitude: [UInt64]

    // MARK: - Initializers

    public init() {
        self.sign = .plus
        self.magnitude = []
    }

    public init(sign: Sign, magnitude: [UInt64]) {
        self.sign = sign
        self.magnitude = magnitude
        self.normalize()
    }

    public init(_ value: Int64) {
        if value == 0 {
            self.sign = .plus
            self.magnitude = []
        } else if value < 0 {
            self.sign = .minus
            if value == Int64.min {
                self.magnitude = [1 << 63]
            } else {
                self.magnitude = [UInt64(-value)]
            }
        } else {
            self.sign = .plus
            self.magnitude = [UInt64(value)]
        }
    }

    public init(_ value: Int) {
        self.init(Int64(value))
    }

    public init(_ value: UInt64) {
        if value == 0 {
            self.sign = .plus
            self.magnitude = []
        } else {
            self.sign = .plus
            self.magnitude = [value]
        }
    }

    public init(integerLiteral value: Int64) {
        self.init(value)
    }

    public init?(_ string: String, radix: Int = 10) {
        var str = string.trimmingCharacters(in: .whitespacesAndNewlines)
        if str.isEmpty { return nil }

        var sign: Sign = .plus
        if str.hasPrefix("-") {
            sign = .minus
            str.removeFirst()
        } else if str.hasPrefix("+") {
            str.removeFirst()
        }

        if str.isEmpty { return nil }

        if radix == 16 && (str.hasPrefix("0x") || str.hasPrefix("0X")) {
            str.removeFirst(2)
        } else if radix == 2 && (str.hasPrefix("0b") || str.hasPrefix("0B")) {
            str.removeFirst(2)
        }

        if str.isEmpty { return nil }

        var result = BigInt.zero
        let bigRadix = BigInt(UInt64(radix))

        for char in str {
            guard let digit = char.hexDigitValue, digit < radix else {
                return nil
            }
            result = result * bigRadix + BigInt(UInt64(digit))
        }

        result.sign = sign
        result.normalize()
        self = result
    }

    // MARK: - Normalization

    private mutating func normalize() {
        while let last = magnitude.last, last == 0 {
            magnitude.removeLast()
        }
        if magnitude.isEmpty {
            sign = .plus
        }
    }

    // MARK: - Constants

    public static let zero = BigInt(0)
    public static let one = BigInt(1)
    public static let minusOne = BigInt(-1)

    public var isZero: Bool {
        return magnitude.isEmpty
    }

    public var isPositive: Bool {
        return sign == .plus && !isZero
    }

    public var isNegative: Bool {
        return sign == .minus && !isZero
    }

    public var isEven: Bool {
        guard let first = magnitude.first else { return true }
        return (first & 1) == 0
    }

    public var isOdd: Bool {
        return !isEven
    }

    // MARK: - Comparison

    public static func < (lhs: BigInt, rhs: BigInt) -> Bool {
        if lhs.sign != rhs.sign {
            return lhs.sign.rawValue < rhs.sign.rawValue
        }
        let magCmp = compareMagnitudes(lhs.magnitude, rhs.magnitude)
        if lhs.sign == .plus {
            return magCmp < 0
        } else {
            return magCmp > 0
        }
    }

    public static func == (lhs: BigInt, rhs: BigInt) -> Bool {
        return lhs.sign == rhs.sign && lhs.magnitude == rhs.magnitude
    }

    private static func compareMagnitudes(_ a: [UInt64], _ b: [UInt64]) -> Int {
        if a.count != b.count {
            return a.count < b.count ? -1 : 1
        }
        for i in stride(from: a.count - 1, through: 0, by: -1) {
            if a[i] != b[i] {
                return a[i] < b[i] ? -1 : 1
            }
        }
        return 0
    }

    // MARK: - Addition & Subtraction

    public static prefix func - (x: BigInt) -> BigInt {
        if x.isZero { return x }
        var result = x
        result.sign = (x.sign == .plus ? .minus : .plus)
        return result
    }

    public static func + (lhs: BigInt, rhs: BigInt) -> BigInt {
        if lhs.isZero { return rhs }
        if rhs.isZero { return lhs }

        if lhs.sign == rhs.sign {
            let mag = addMagnitudes(lhs.magnitude, rhs.magnitude)
            return BigInt(sign: lhs.sign, magnitude: mag)
        } else {
            let cmp = compareMagnitudes(lhs.magnitude, rhs.magnitude)
            if cmp == 0 {
                return BigInt.zero
            } else if cmp > 0 {
                let mag = subMagnitudes(lhs.magnitude, rhs.magnitude)
                return BigInt(sign: lhs.sign, magnitude: mag)
            } else {
                let mag = subMagnitudes(rhs.magnitude, lhs.magnitude)
                return BigInt(sign: rhs.sign, magnitude: mag)
            }
        }
    }

    public static func - (lhs: BigInt, rhs: BigInt) -> BigInt {
        return lhs + (-rhs)
    }

    private static func addMagnitudes(_ a: [UInt64], _ b: [UInt64]) -> [UInt64] {
        var result: [UInt64] = []
        let count = max(a.count, b.count)
        result.reserveCapacity(count + 1)

        var carry: UInt64 = 0
        for i in 0..<count {
            let ai = i < a.count ? a[i] : 0
            let bi = i < b.count ? b[i] : 0

            let (sum1, overflow1) = ai.addingReportingOverflow(bi)
            let (sum2, overflow2) = sum1.addingReportingOverflow(carry)
            carry = (overflow1 ? 1 : 0) + (overflow2 ? 1 : 0)
            result.append(sum2)
        }
        if carry > 0 {
            result.append(carry)
        }
        return result
    }

    private static func subMagnitudes(_ a: [UInt64], _ b: [UInt64]) -> [UInt64] {
        var result: [UInt64] = []
        result.reserveCapacity(a.count)

        var borrow: UInt64 = 0
        for i in 0..<a.count {
            let ai = a[i]
            let bi = i < b.count ? b[i] : 0

            let (diff1, overflow1) = ai.subtractingReportingOverflow(borrow)
            let (diff2, overflow2) = diff1.subtractingReportingOverflow(bi)
            borrow = (overflow1 ? 1 : 0) + (overflow2 ? 1 : 0)
            result.append(diff2)
        }
        while let last = result.last, last == 0 {
            result.removeLast()
        }
        return result
    }

    // MARK: - Multiplication

    public static func * (lhs: BigInt, rhs: BigInt) -> BigInt {
        if lhs.isZero || rhs.isZero { return BigInt.zero }

        let sign: Sign = (lhs.sign == rhs.sign ? .plus : .minus)
        let mag: [UInt64]
        if lhs.magnitude.count < 32 || rhs.magnitude.count < 32 {
            mag = multiplySchoolbook(lhs.magnitude, rhs.magnitude)
        } else {
            mag = multiplyKaratsuba(lhs.magnitude, rhs.magnitude)
        }
        return BigInt(sign: sign, magnitude: mag)
    }

    private static func multiplySchoolbook(_ a: [UInt64], _ b: [UInt64]) -> [UInt64] {
        var result = [UInt64](repeating: 0, count: a.count + b.count)
        for i in 0..<a.count {
            var carry: UInt64 = 0
            let ai = a[i]
            if ai == 0 { continue }
            for j in 0..<b.count {
                let bj = b[j]
                let (high, low) = ai.multipliedFullWidth(by: bj)
                let (s1, o1) = low.addingReportingOverflow(carry)
                let (s2, o2) = s1.addingReportingOverflow(result[i + j])
                result[i + j] = s2
                carry = high &+ (o1 ? 1 : 0) &+ (o2 ? 1 : 0)
            }
            if carry > 0 {
                result[i + b.count] += carry
            }
        }
        while let last = result.last, last == 0 {
            result.removeLast()
        }
        return result
    }

    private static func multiplyKaratsuba(_ a: [UInt64], _ b: [UInt64]) -> [UInt64] {
        let n = max(a.count, b.count)
        if n < 32 {
            return multiplySchoolbook(a, b)
        }
        let m = (n + 1) / 2

        let a0 = Array(a.prefix(min(m, a.count)))
        let a1 = a.count > m ? Array(a.suffix(from: m)) : []
        let b0 = Array(b.prefix(min(m, b.count)))
        let b1 = b.count > m ? Array(b.suffix(from: m)) : []

        let z0 = multiplyKaratsuba(a0, b0)
        let z2 = multiplyKaratsuba(a1, b1)

        let a0_plus_a1 = addMagnitudes(a0, a1)
        let b0_plus_b1 = addMagnitudes(b0, b1)
        let z1_raw = multiplyKaratsuba(a0_plus_a1, b0_plus_b1)

        // z1 = z1_raw - z0 - z2
        let z1_sub_z0 = subMagnitudes(z1_raw, z0)
        let z1 = subMagnitudes(z1_sub_z0, z2)

        var result = [UInt64](repeating: 0, count: 2 * m + z2.count + 1)

        // Add z0
        for i in 0..<z0.count {
            result[i] = z0[i]
        }

        // Add z1 shifted by m
        var carry: UInt64 = 0
        for i in 0..<z1.count {
            let (sum1, ov1) = result[i + m].addingReportingOverflow(z1[i])
            let (sum2, ov2) = sum1.addingReportingOverflow(carry)
            result[i + m] = sum2
            carry = (ov1 ? 1 : 0) + (ov2 ? 1 : 0)
        }
        var idx = z1.count + m
        while carry > 0 && idx < result.count {
            let (sum, ov) = result[idx].addingReportingOverflow(carry)
            result[idx] = sum
            carry = ov ? 1 : 0
            idx += 1
        }

        // Add z2 shifted by 2*m
        carry = 0
        for i in 0..<z2.count {
            let (sum1, ov1) = result[i + 2 * m].addingReportingOverflow(z2[i])
            let (sum2, ov2) = sum1.addingReportingOverflow(carry)
            result[i + 2 * m] = sum2
            carry = (ov1 ? 1 : 0) + (ov2 ? 1 : 0)
        }
        idx = z2.count + 2 * m
        while carry > 0 && idx < result.count {
            let (sum, ov) = result[idx].addingReportingOverflow(carry)
            result[idx] = sum
            carry = ov ? 1 : 0
            idx += 1
        }

        while let last = result.last, last == 0 {
            result.removeLast()
        }
        return result
    }

    // MARK: - Division & Modulo

    public static func / (lhs: BigInt, rhs: BigInt) -> BigInt {
        precondition(!rhs.isZero, "Division by zero in BigInt")
        return lhs.quotientAndRemainder(dividingBy: rhs).quotient
    }

    public static func % (lhs: BigInt, rhs: BigInt) -> BigInt {
        precondition(!rhs.isZero, "Modulo by zero in BigInt")
        return lhs.quotientAndRemainder(dividingBy: rhs).remainder
    }

    public func quotientAndRemainder(dividingBy rhs: BigInt) -> (quotient: BigInt, remainder: BigInt) {
        precondition(!rhs.isZero, "Division by zero")
        if self.isZero {
            return (BigInt.zero, BigInt.zero)
        }
        let cmp = BigInt.compareMagnitudes(self.magnitude, rhs.magnitude)
        if cmp < 0 {
            return (BigInt.zero, self)
        }
        if cmp == 0 {
            let qSign: Sign = (self.sign == rhs.sign ? .plus : .minus)
            return (BigInt(sign: qSign, magnitude: [1]), BigInt.zero)
        }

        let (qMag, rMag) = divideBinary(self.magnitude, rhs.magnitude)
        let qSign: Sign = (self.sign == rhs.sign ? .plus : .minus)
        let rSign: Sign = self.sign

        return (BigInt(sign: qSign, magnitude: qMag), BigInt(sign: rSign, magnitude: rMag))
    }

    /// Binary long division algorithm for arbitrary magnitude arrays
    private func divideBinary(_ u: [UInt64], _ v: [UInt64]) -> ([UInt64], [UInt64]) {
        if v.count == 1 {
            let divisor = v[0]
            var quotient = [UInt64](repeating: 0, count: u.count)
            var remainder: UInt64 = 0
            for i in stride(from: u.count - 1, through: 0, by: -1) {
                let (q, r) = divisor.dividingFullWidth((high: remainder, low: u[i]))
                quotient[i] = q
                remainder = r
            }
            while let last = quotient.last, last == 0 {
                quotient.removeLast()
            }
            let remList = remainder == 0 ? [] : [remainder]
            return (quotient, remList)
        }

        // Bitwise binary long division
        var rem = [UInt64]()
        let totalBits = u.count * 64
        var quotient = [UInt64](repeating: 0, count: u.count)

        for bitIndex in stride(from: totalBits - 1, through: 0, by: -1) {
            let limbIdx = bitIndex / 64
            let bitOffset = bitIndex % 64
            let bit = (u[limbIdx] >> bitOffset) & 1

            // rem = (rem << 1) | bit
            rem = shiftLeftLimbArray(rem, bits: 1)
            if bit == 1 {
                if rem.isEmpty {
                    rem = [1]
                } else {
                    rem[0] |= 1
                }
            }

            if BigInt.compareMagnitudes(rem, v) >= 0 {
                rem = BigInt.subMagnitudes(rem, v)
                quotient[limbIdx] |= (1 << bitOffset)
            }
        }

        while let last = quotient.last, last == 0 {
            quotient.removeLast()
        }
        while let last = rem.last, last == 0 {
            rem.removeLast()
        }

        return (quotient, rem)
    }

    private func shiftLeftLimbArray(_ a: [UInt64], bits: Int) -> [UInt64] {
        if bits == 0 { return a }
        let limbShift = bits / 64
        let bitShift = UInt64(bits % 64)
        var result = [UInt64](repeating: 0, count: a.count + limbShift + 1)

        var carry: UInt64 = 0
        for i in 0..<a.count {
            let val = a[i]
            if bitShift == 0 {
                result[i + limbShift] = val
            } else {
                result[i + limbShift] = (val << bitShift) | carry
                carry = val >> (64 - bitShift)
            }
        }
        if carry > 0 {
            result[a.count + limbShift] = carry
        }
        while let last = result.last, last == 0 {
            result.removeLast()
        }
        return result
    }

    private func shiftRightLimbArray(_ a: [UInt64], bits: Int) -> [UInt64] {
        if bits == 0 { return a }
        let limbShift = bits / 64
        let bitShift = UInt64(bits % 64)
        if limbShift >= a.count { return [] }

        var result: [UInt64] = []
        result.reserveCapacity(a.count - limbShift)

        var carry: UInt64 = 0
        for i in stride(from: a.count - 1, through: limbShift, by: -1) {
            let val = a[i]
            if bitShift == 0 {
                result.append(val)
            } else {
                let current = (val >> bitShift) | carry
                result.append(current)
                carry = val << (64 - bitShift)
            }
        }
        result.reverse()
        while let last = result.last, last == 0 {
            result.removeLast()
        }
        return result
    }

    // MARK: - Number-Theoretic Functions

    public static func gcd(_ a: BigInt, _ b: BigInt) -> BigInt {
        var x = a.magnitude.isEmpty ? BigInt.zero : BigInt(sign: .plus, magnitude: a.magnitude)
        var y = b.magnitude.isEmpty ? BigInt.zero : BigInt(sign: .plus, magnitude: b.magnitude)

        while !y.isZero {
            let r = x % y
            x = y
            y = r
        }
        return x
    }

    public static func lcm(_ a: BigInt, _ b: BigInt) -> BigInt {
        if a.isZero || b.isZero { return BigInt.zero }
        let g = gcd(a, b)
        return (a / g) * b
    }

    public func power(_ exponent: Int) -> BigInt {
        precondition(exponent >= 0, "Negative exponent in BigInt.power")
        if exponent == 0 { return BigInt.one }
        if exponent == 1 { return self }

        var base = self
        var exp = exponent
        var result = BigInt.one

        while exp > 0 {
            if (exp & 1) == 1 {
                result = result * base
            }
            base = base * base
            exp >>= 1
        }
        return result
    }

    // MARK: - Bitwise Logic

    public static func & (lhs: BigInt, rhs: BigInt) -> BigInt {
        let maxCount = max(lhs.magnitude.count, rhs.magnitude.count)
        var mag: [UInt64] = []
        mag.reserveCapacity(maxCount)

        for i in 0..<maxCount {
            let l = i < lhs.magnitude.count ? lhs.magnitude[i] : 0
            let r = i < rhs.magnitude.count ? rhs.magnitude[i] : 0
            mag.append(l & r)
        }
        return BigInt(sign: (lhs.sign == .minus && rhs.sign == .minus) ? .minus : .plus, magnitude: mag)
    }

    public static func | (lhs: BigInt, rhs: BigInt) -> BigInt {
        let maxCount = max(lhs.magnitude.count, rhs.magnitude.count)
        var mag: [UInt64] = []
        mag.reserveCapacity(maxCount)

        for i in 0..<maxCount {
            let l = i < lhs.magnitude.count ? lhs.magnitude[i] : 0
            let r = i < rhs.magnitude.count ? rhs.magnitude[i] : 0
            mag.append(l | r)
        }
        return BigInt(sign: (lhs.sign == .minus || rhs.sign == .minus) ? .minus : .plus, magnitude: mag)
    }

    public static func ^ (lhs: BigInt, rhs: BigInt) -> BigInt {
        let maxCount = max(lhs.magnitude.count, rhs.magnitude.count)
        var mag: [UInt64] = []
        mag.reserveCapacity(maxCount)

        for i in 0..<maxCount {
            let l = i < lhs.magnitude.count ? lhs.magnitude[i] : 0
            let r = i < rhs.magnitude.count ? rhs.magnitude[i] : 0
            mag.append(l ^ r)
        }
        let sign: Sign = (lhs.sign != rhs.sign) ? .minus : .plus
        return BigInt(sign: sign, magnitude: mag)
    }

    public static func << (lhs: BigInt, rhs: Int) -> BigInt {
        if lhs.isZero || rhs == 0 { return lhs }
        precondition(rhs >= 0, "Negative bit shift count")
        let shifted = lhs.shiftLeftLimbArray(lhs.magnitude, bits: rhs)
        return BigInt(sign: lhs.sign, magnitude: shifted)
    }

    public static func >> (lhs: BigInt, rhs: Int) -> BigInt {
        if lhs.isZero || rhs == 0 { return lhs }
        precondition(rhs >= 0, "Negative bit shift count")
        let shifted = lhs.shiftRightLimbArray(lhs.magnitude, bits: rhs)
        return BigInt(sign: lhs.sign, magnitude: shifted)
    }

    // MARK: - Conversions & Display

    public var description: String {
        if isZero { return "0" }
        var temp = BigInt(sign: .plus, magnitude: self.magnitude)
        let bigTen = BigInt(10)
        var digits: [Character] = []

        while !temp.isZero {
            let (q, r) = temp.quotientAndRemainder(dividingBy: bigTen)
            let d = r.magnitude.first ?? 0
            digits.append(Character(String(d)))
            temp = q
        }

        if sign == .minus {
            digits.append("-")
        }
        return String(digits.reversed())
    }

    public var asInt64: Int64? {
        if isZero { return 0 }
        guard magnitude.count == 1 else { return nil }
        let limb = magnitude[0]
        if sign == .plus {
            if limb <= UInt64(Int64.max) {
                return Int64(limb)
            }
        } else {
            if limb <= UInt64(Int64.max) + 1 {
                return -Int64(limb)
            }
        }
        return nil
    }

    public var asInt: Int? {
        guard let i64 = asInt64 else { return nil }
        return Int(exactly: i64)
    }

    public var bitWidth: Int {
        if isZero { return 0 }
        let topLimbBits = 64 - magnitude.last!.leadingZeroBitCount
        return (magnitude.count - 1) * 64 + topLimbBits
    }
}
