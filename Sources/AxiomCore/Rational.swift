import Foundation

/// Exact rational number arithmetic over the field of fractions Q = { p / q | p, q in Z, q > 0, gcd(p, q) = 1 }.
/// Prevents numerical drift and precision issues in Simplex tableau computations.
public struct Rational: Comparable, Hashable, CustomStringConvertible, ExpressibleByIntegerLiteral, ExpressibleByFloatLiteral, Sendable {
    /// Canonical numerator
    public let numerator: BigInt

    /// Canonical denominator (strictly positive)
    public let denominator: BigInt

    // MARK: - Initializers

    public init() {
        self.numerator = BigInt.zero
        self.denominator = BigInt.one
    }

    public init(_ num: BigInt, _ den: BigInt = BigInt.one) {
        precondition(!den.isZero, "Denominator of Rational cannot be zero")
        if num.isZero {
            self.numerator = BigInt.zero
            self.denominator = BigInt.one
            return
        }

        var p = num
        var q = den
        if q.isNegative {
            p = -p
            q = -q
        }

        let g = BigInt.gcd(p, q)
        if g > BigInt.one {
            self.numerator = p / g
            self.denominator = q / g
        } else {
            self.numerator = p
            self.denominator = q
        }
    }

    public init(_ value: Int64) {
        self.init(BigInt(value), BigInt.one)
    }

    public init(_ value: Int) {
        self.init(BigInt(value), BigInt.one)
    }

    public init(integerLiteral value: Int64) {
        self.init(value)
    }

    public init(floatLiteral value: Double) {
        self.init(value)
    }

    public init(_ doubleVal: Double) {
        if doubleVal.isNaN || doubleVal.isInfinite {
            self.init(BigInt.zero, BigInt.one)
            return
        }
        if doubleVal == 0.0 {
            self.init(BigInt.zero, BigInt.one)
            return
        }

        let isNeg = doubleVal < 0
        let absVal = Swift.abs(doubleVal)

        // Exact rational conversion from IEEE-754 bit pattern
        let bits = absVal.bitPattern
        let exponent = Int((bits >> 52) & 0x7FF) - 1023
        let fraction = bits & 0x000FFFFFFFFFFFFF

        let mantissa: UInt64
        let exp: Int
        if exponent == -1023 {
            // Subnormal
            mantissa = fraction
            exp = -1022 - 52
        } else {
            // Normal
            mantissa = fraction | (1 << 52)
            exp = exponent - 52
        }

        var num = BigInt(mantissa)
        var den = BigInt.one

        if exp >= 0 {
            num = num << exp
        } else {
            den = den << (-exp)
        }

        if isNeg {
            num = -num
        }
        self.init(num, den)
    }

    public init?(_ string: String) {
        let str = string.trimmingCharacters(in: .whitespacesAndNewlines)
        if str.isEmpty { return nil }

        // Check for fraction format "p/q"
        if let slashIdx = str.firstIndex(of: "/") {
            let numStr = String(str[..<slashIdx])
            let denStr = String(str[str.index(after: slashIdx)...])
            guard let n = BigInt(numStr), let d = BigInt(denStr), !d.isZero else {
                return nil
            }
            self.init(n, d)
            return
        }

        // Check for decimal format "123.456"
        if let dotIdx = str.firstIndex(of: ".") {
            let wholeStr = String(str[..<dotIdx])
            let fracStr = String(str[str.index(after: dotIdx)...])

            var signMultiplier: Int64 = 1
            var wholePart = wholeStr
            if wholePart.hasPrefix("-") {
                signMultiplier = -1
                wholePart.removeFirst()
            } else if wholePart.hasPrefix("+") {
                wholePart.removeFirst()
            }

            guard let wholeBig = BigInt(wholePart.isEmpty ? "0" : wholePart),
                  let fracBig = BigInt(fracStr.isEmpty ? "0" : fracStr) else {
                return nil
            }

            let numDecimals = fracStr.count
            let ten = BigInt(10)
            let den = ten.power(numDecimals)
            let num = wholeBig * den + fracBig
            let finalNum = signMultiplier == -1 ? -num : num
            self.init(finalNum, den)
            return
        }

        // Standard integer string
        guard let n = BigInt(str) else { return nil }
        self.init(n, BigInt.one)
    }

    // MARK: - Constants

    public static let zero = Rational(BigInt.zero, BigInt.one)
    public static let one = Rational(BigInt.one, BigInt.one)
    public static let minusOne = Rational(BigInt.minusOne, BigInt.one)

    public var isZero: Bool {
        return numerator.isZero
    }

    public var isPositive: Bool {
        return numerator.isPositive
    }

    public var isNegative: Bool {
        return numerator.isNegative
    }

    public var isInteger: Bool {
        return denominator == BigInt.one
    }

    // MARK: - Comparison

    public static func < (lhs: Rational, rhs: Rational) -> Bool {
        // a / b < c / d <=> a * d < c * b (since b, d > 0)
        return (lhs.numerator * rhs.denominator) < (rhs.numerator * lhs.denominator)
    }

    public static func == (lhs: Rational, rhs: Rational) -> Bool {
        return lhs.numerator == rhs.numerator && lhs.denominator == rhs.denominator
    }

    // MARK: - Arithmetic

    public static prefix func - (x: Rational) -> Rational {
        return Rational(-x.numerator, x.denominator)
    }

    public static func + (lhs: Rational, rhs: Rational) -> Rational {
        if lhs.isZero { return rhs }
        if rhs.isZero { return lhs }
        let num = lhs.numerator * rhs.denominator + rhs.numerator * lhs.denominator
        let den = lhs.denominator * rhs.denominator
        return Rational(num, den)
    }

    public static func - (lhs: Rational, rhs: Rational) -> Rational {
        return lhs + (-rhs)
    }

    public static func * (lhs: Rational, rhs: Rational) -> Rational {
        if lhs.isZero || rhs.isZero { return Rational.zero }
        let num = lhs.numerator * rhs.numerator
        let den = lhs.denominator * rhs.denominator
        return Rational(num, den)
    }

    public static func / (lhs: Rational, rhs: Rational) -> Rational {
        precondition(!rhs.isZero, "Division by zero in Rational")
        let num = lhs.numerator * rhs.denominator
        let den = lhs.denominator * rhs.numerator
        return Rational(num, den)
    }

    public var reciprocal: Rational {
        precondition(!isZero, "Reciprocal of zero Rational is undefined")
        return Rational(denominator, numerator)
    }

    public var absoluteValue: Rational {
        return isNegative ? -self : self
    }

    // MARK: - Rounding and Conversion

    public var floor: BigInt {
        if denominator == BigInt.one { return numerator }
        if numerator.isPositive {
            return numerator / denominator
        } else {
            return (numerator - denominator + BigInt.one) / denominator
        }
    }

    public var ceil: BigInt {
        if denominator == BigInt.one { return numerator }
        if numerator.isPositive {
            return (numerator + denominator - BigInt.one) / denominator
        } else {
            return numerator / denominator
        }
    }

    public var asDouble: Double {
        guard let numDouble = Double(numerator.description),
              let denDouble = Double(denominator.description) else {
            return Double.nan
        }
        return numDouble / denDouble
    }

    public var description: String {
        if denominator == BigInt.one {
            return numerator.description
        }
        return "\(numerator)/\(denominator)"
    }
}
