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

runner.suite("BitVector QF_BV Bitwise & Modular Arithmetic") {
    runner.test("Initialization and binary string parsing") {
        let bv = BitVector(binaryString: "#b10110010")!
        runner.expectEqual(bv.width, 8)
        runner.expectEqual(bv.asUInt64, 0b10110010)
        runner.expectEqual(bv.description, "#b10110010")
        runner.expectTrue(bv.msb)
        runner.expectFalse(bv.lsb)
    }

    runner.test("Bitwise logic operators") {
        let a = BitVector(width: 8, value: 0b11001010)
        let b = BitVector(width: 8, value: 0b10101100)
        runner.expectEqual(a & b, BitVector(width: 8, value: 0b10001000))
        runner.expectEqual(a | b, BitVector(width: 8, value: 0b11101110))
        runner.expectEqual(a ^ b, BitVector(width: 8, value: 0b01100110))
        runner.expectEqual(~a, BitVector(width: 8, value: 0b00110101))
    }

    runner.test("Shifts and Rotates") {
        let bv = BitVector(width: 8, value: 0b11001001)
        runner.expectEqual(bv.shiftLeft(by: 2), BitVector(width: 8, value: 0b00100100))
        runner.expectEqual(bv.logicalShiftRight(by: 2), BitVector(width: 8, value: 0b00110010))
        runner.expectEqual(bv.arithmeticShiftRight(by: 2), BitVector(width: 8, value: 0b11110010))
        runner.expectEqual(bv.rotateLeft(by: 1), BitVector(width: 8, value: 0b10010011))
    }

    runner.test("Slice extraction and concatenation") {
        let bv = BitVector(width: 8, value: 0b11010010)
        let sub = bv.extract(high: 5, low: 2) // bits 5..2: 0100
        runner.expectEqual(sub.width, 4)
        runner.expectEqual(sub.asUInt64, 0b0100)

        let a = BitVector(width: 4, value: 0b1010)
        let b = BitVector(width: 4, value: 0b0101)
        let c = BitVector.concat(a, b) // 10100101
        runner.expectEqual(c.width, 8)
        runner.expectEqual(c.asUInt64, 0b10100101)
    }

    runner.test("Modular 2^w arithmetic and overflow wrapping") {
        let maxU8 = BitVector(width: 8, value: 255)
        let one = BitVector(width: 8, value: 1)
        runner.expectEqual(maxU8 + one, BitVector(width: 8, value: 0))

        let a = BitVector(width: 8, value: 20)
        let b = BitVector(width: 8, value: 6)
        let (q, r) = a.unsignedDividingBy(b)
        runner.expectEqual(q, BitVector(width: 8, value: 3))
        runner.expectEqual(r, BitVector(width: 8, value: 2))
    }

    runner.test("Signed vs unsigned comparisons") {
        let minusOne = BitVector(width: 8, value: 0xFF)
        let plusOne = BitVector(width: 8, value: 1)

        runner.expectTrue(plusOne.unsignedLessThan(minusOne))
        runner.expectTrue(minusOne.signedLessThan(plusOne))
    }
}

runner.suite("Symbol Interning and Scoped Tables") {
    runner.test("Global symbol pool uniqueness and O(1) equality") {
        let s1 = Symbol("x")
        let s2 = Symbol("x")
        let s3 = Symbol("y")

        runner.expectEqual(s1, s2)
        runner.expectEqual(s1.id, s2.id)
        runner.expectNotEqual(s1, s3)
        runner.expectEqual(s1.name, "x")
        runner.expectEqual(s3.name, "y")
    }

    runner.test("Scoped SymbolTable push/pop and shadowing") {
        let table = SymbolTable<Int>()
        let symX = Symbol("x")
        let symY = Symbol("y")

        table.insert(symbol: symX, value: 10)
        table.insert(symbol: symY, value: 20)
        runner.expectEqual(table.lookup(symbol: symX), 10)

        // Push inner scope
        table.pushScope()
        table.insert(symbol: symX, value: 99) // shadowed
        runner.expectEqual(table.lookup(symbol: symX), 99)
        runner.expectEqual(table.lookup(symbol: symY), 20) // parent visible

        // Pop inner scope
        table.popScope()
        runner.expectEqual(table.lookup(symbol: symX), 10) // restored
    }
}

runner.suite("ArenaAllocator Monotonic Memory Management") {
    runner.test("Contiguous allocation and typed creation") {
        let arena = ArenaAllocator(chunkSize: 1024)
        let ptr1 = arena.create(42)
        let ptr2 = arena.create(100)
        runner.expectEqual(ptr1.pointee, 42)
        runner.expectEqual(ptr2.pointee, 100)

        arena.reset()
        runner.expectEqual(arena.bytesAllocated, 0)
    }
}

runner.reportAndExit()
