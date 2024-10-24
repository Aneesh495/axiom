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

runner.reportAndExit()
