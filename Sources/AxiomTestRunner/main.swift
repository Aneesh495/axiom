import Foundation
import AxiomCore

let runner = TestHarness.shared

runner.suite("BigInt Arithmetic and Logic") {
    runner.test("Basic arithmetic operators") {
        let a = BigInt(42)
        let b = BigInt(17)
        runner.expectEqual(a + b, BigInt(59))
        runner.expectEqual(a - b, BigInt(25))
        runner.expectEqual(a * b, BigInt(714))
        runner.expectEqual(a / b, BigInt(2))
        runner.expectEqual(a % b, BigInt(8))
    }

    runner.test("Negative integer arithmetic") {
        let a = BigInt(-42)
        let b = BigInt(17)
        runner.expectEqual(a + b, BigInt(-25))
        runner.expectEqual(a - b, BigInt(-59))
        runner.expectEqual(a * b, BigInt(-714))
        runner.expectEqual(a / b, BigInt(-2))
        runner.expectEqual(a % b, BigInt(-8))
    }

    runner.test("Multi-limb multiplication and division") {
        let a = BigInt("123456789012345678901234567890")!
        let b = BigInt("987654321098765432109876543210")!
        let prod = a * b
        runner.expectEqual(prod / b, a)
        runner.expectEqual(prod % b, BigInt.zero)
        runner.expectEqual(prod / a, b)
    }

    runner.test("Greatest common divisor and least common multiple") {
        let a = BigInt(1071)
        let b = BigInt(462)
        runner.expectEqual(BigInt.gcd(a, b), BigInt(21))
        runner.expectEqual(BigInt.lcm(BigInt(12), BigInt(18)), BigInt(36))
    }

    runner.test("Powers and bitwise shifts") {
        let two = BigInt(2)
        runner.expectEqual(two.power(10), BigInt(1024))
        runner.expectEqual(two.power(0), BigInt(1))
        runner.expectEqual(two.power(1), BigInt(2))
        runner.expectEqual((BigInt(1) << 10), BigInt(1024))
        runner.expectEqual((BigInt(1024) >> 4), BigInt(64))
    }

    runner.test("Decimal string parsing and roundtrip") {
        let original = "-987654321098765432109876543210123456789"
        let val = BigInt(original)!
        runner.expectEqual(val.description, original)
    }
}

runner.suite("Rational Exact Fractions") {
    runner.test("Canonical simplification and reduction") {
        let r1 = Rational(BigInt(14), BigInt(21))
        runner.expectEqual(r1.numerator, BigInt(2))
        runner.expectEqual(r1.denominator, BigInt(3))
        runner.expectEqual(r1.description, "2/3")

        let r2 = Rational(BigInt(-10), BigInt(-25))
        runner.expectEqual(r2.numerator, BigInt(2))
        runner.expectEqual(r2.denominator, BigInt(5))
    }

    runner.test("Arithmetic operations") {
        let a = Rational(1, 3)
        let b = Rational(1, 6)
        runner.expectEqual(a + b, Rational(1, 2))
        runner.expectEqual(a - b, Rational(1, 6))
        runner.expectEqual(a * b, Rational(1, 18))
        runner.expectEqual(a / b, Rational(2, 1))
    }

    runner.test("Exact comparisons") {
        let a = Rational(1, 3)
        let b = Rational(1, 2)
        let c = Rational(2, 6)
        runner.expectTrue(a < b)
        runner.expectTrue(b > a)
        runner.expectEqual(a, c)
    }

    runner.test("Floor and Ceil rounding") {
        let pos = Rational(7, 3) // 2.333...
        runner.expectEqual(pos.floor, BigInt(2))
        runner.expectEqual(pos.ceil, BigInt(3))

        let neg = Rational(-7, 3) // -2.333...
        runner.expectEqual(neg.floor, BigInt(-3))
        runner.expectEqual(neg.ceil, BigInt(-2))
    }

    runner.test("Decimal and string conversions") {
        let r1 = Rational("0.75")!
        runner.expectEqual(r1, Rational(3, 4))

        let r2 = Rational("-125/250")!
        runner.expectEqual(r2, Rational(-1, 2))
    }
}

runner.reportAndExit()
