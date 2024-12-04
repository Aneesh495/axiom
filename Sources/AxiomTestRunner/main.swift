import Foundation
import AxiomCore
import AxiomAST

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

runner.suite("DisjointSet Backtrackable Union-Find & Proof Forest") {
    runner.test("Basic union and equivalence") {
        let uf = DisjointSet()
        let a = uf.makeSet()
        let b = uf.makeSet()
        let c = uf.makeSet()
        let d = uf.makeSet()

        runner.expectFalse(uf.areEquivalent(a, b))
        uf.union(a, b, reason: 101)
        runner.expectTrue(uf.areEquivalent(a, b))

        uf.union(b, c, reason: 102)
        runner.expectTrue(uf.areEquivalent(a, c))
        runner.expectFalse(uf.areEquivalent(a, d))
    }

    runner.test("Proof forest conflict explanation") {
        let uf = DisjointSet()
        let a = uf.makeSet()
        let b = uf.makeSet()
        let c = uf.makeSet()

        uf.union(a, b, reason: 42)
        uf.union(b, c, reason: 84)

        let reasonsBC = uf.explainEquivalence(b, c)
        runner.expectTrue(reasonsBC.contains(42))
        runner.expectTrue(reasonsBC.contains(84))

        let reasonsAB = uf.explainEquivalence(a, b)
        runner.expectTrue(reasonsAB.contains(42))
        runner.expectEqual(reasonsAB.count, 1)
    }

    runner.test("Checkpoints and backtracking restoration") {
        let uf = DisjointSet()
        let a = uf.makeSet()
        let b = uf.makeSet()
        let c = uf.makeSet()

        uf.union(a, b, reason: 1)
        runner.expectTrue(uf.areEquivalent(a, b))

        let cp = uf.pushCheckpoint()
        uf.union(b, c, reason: 2)
        runner.expectTrue(uf.areEquivalent(a, c))

        // Backtrack to checkpoint
        uf.popCheckpoint(to: cp)
        runner.expectTrue(uf.areEquivalent(a, b))
        runner.expectFalse(uf.areEquivalent(a, c))
        runner.expectFalse(uf.areEquivalent(b, c))
    }
}

runner.suite("IndexedPriorityQueue SAT VSIDS Heuristics") {
    runner.test("Max-heap extraction and O(log n) decrease-key") {
        var pq = IndexedPriorityQueue<String, Double>.maxHeap()
        pq.insert(element: "v1", priority: 1.5)
        pq.insert(element: "v2", priority: 3.2)
        pq.insert(element: "v3", priority: 0.8)

        runner.expectEqual(pq.peek()?.element, "v2")
        // Bump v3 activity score
        pq.updatePriority(element: "v3", newPriority: 5.0)
        runner.expectEqual(pq.peek()?.element, "v3")

        let first = pq.pop()
        runner.expectEqual(first?.element, "v3")
        runner.expectEqual(first?.priority, 5.0)

        let second = pq.pop()
        runner.expectEqual(second?.element, "v2")
        runner.expectEqual(second?.priority, 3.2)
    }
}

runner.suite("BitSet Dense Visited Sets & Word Packing") {
    runner.test("Insertion, popcount, and iterator traversal") {
        var bs = BitSet(capacity: 256)
        bs.insert(5)
        bs.insert(63)
        bs.insert(64)
        bs.insert(128)

        runner.expectEqual(bs.count, 4)
        runner.expectTrue(bs.contains(5))
        runner.expectTrue(bs.contains(64))
        runner.expectFalse(bs.contains(65))

        let elements = Array(bs)
        runner.expectEqual(elements, [5, 63, 64, 128])
    }

    runner.test("BitSet set algebra: union and intersection") {
        var s1 = BitSet(capacity: 128)
        var s2 = BitSet(capacity: 128)
        s1.insert(10)
        s1.insert(20)
        s2.insert(20)
        s2.insert(30)

        var u = s1
        u.formUnion(s2)
        runner.expectEqual(u.count, 3)

        var i = s1
        i.formIntersection(s2)
        runner.expectEqual(i.count, 1)
        runner.expectTrue(i.contains(20))
    }
}

runner.suite("RingBuffer Rolling Diagnostics") {
    runner.test("Sliding window average and circular overwrite") {
        var rb = RingBuffer<Double>(capacity: 3)
        rb.push(10.0)
        rb.push(20.0)
        runner.expectEqual(rb.average, 15.0)

        rb.push(30.0)
        runner.expectEqual(rb.average, 20.0)

        // Overwrite 10.0 with 40.0 -> [40, 20, 30] -> avg 30.0
        rb.push(40.0)
        runner.expectEqual(rb.count, 3)
        runner.expectEqual(rb.average, 30.0)
    }
}

runner.suite("AxiomAST Sorts and Expr Representations") {
    runner.test("Sort inference and bit-vector widths") {
        let x = Expr.variable("x", .bitVec(width: 32))
        let y = Expr.variable("y", .bitVec(width: 32))
        let add = Expr.bvAdd(x, y)
        runner.expectEqual(add.sort, .bitVec(width: 32))

        let arr = Expr.variable("mem", .array(index: .int, element: .real))
        let sel = Expr.select(array: arr, index: .int(5))
        runner.expectEqual(sel.sort, .real)
    }

    runner.test("Free variables extraction") {
        let x = Symbol("x")
        let y = Symbol("y")
        let expr = Expr.and([
            Expr.lt(.variable(name: x, sort: .int), .int(10)),
            Expr.eq(.variable(name: y, sort: .int), .int(20))
        ])
        let vars = expr.freeVariables
        runner.expectEqual(vars.count, 2)
        runner.expectTrue(vars.contains(x))
        runner.expectTrue(vars.contains(y))
    }
}

runner.suite("AxiomAST Term Simplification and Constant Folding") {
    let simplifier = TermSimplifier()

    runner.test("Boolean algebraic identities") {
        let p = Expr.variable("p", .bool)
        // p and true -> p
        runner.expectEqual(simplifier.simplify(.and([p, .true])), p)
        // p and false -> false
        runner.expectEqual(simplifier.simplify(.and([p, .false])), .false)
        // not(not(p)) -> p
        runner.expectEqual(simplifier.simplify(.not(.not(p))), p)
        // p or not(p) -> true
        runner.expectEqual(simplifier.simplify(.or([p, .not(p)])), .true)
    }

    runner.test("Arithmetic constant folding") {
        let e1 = Expr.add([.int(10), .int(25), Expr.variable("x", .int)])
        let s1 = simplifier.simplify(e1)
        runner.expectEqual(s1, .add([Expr.variable("x", .int), .int(35)]))

        let e2 = Expr.sub(.int(50), .int(18))
        runner.expectEqual(simplifier.simplify(e2), .int(32))
    }

    runner.test("Bit-Vector identities and constant evaluation") {
        let x = Expr.variable("x", .bitVec(width: 8))
        // x ^ x -> 0
        runner.expectEqual(simplifier.simplify(.bvXor(x, x)), .bv(width: 8, value: 0))

        let c1 = Expr.bv(width: 8, value: 0x0F)
        let c2 = Expr.bv(width: 8, value: 0xF0)
        runner.expectEqual(simplifier.simplify(.bvOr(c1, c2)), .bv(width: 8, value: 0xFF))
    }
}

runner.suite("AxiomAST Normal Forms & Tseitin Transformation") {
    let nnf = NormalForms()
    let tseitin = TseitinTransformer()

    runner.test("De Morgan push to NNF") {
        let p = Expr.variable("p", .bool)
        let q = Expr.variable("q", .bool)
        // not(p and q) -> not p or not q
        let expr = Expr.not(.and([p, q]))
        let result = nnf.toNNF(expr)
        runner.expectEqual(result, .or([.not(p), .not(q)]))
    }

    runner.test("Linear Tseitin CNF encoding") {
        let a = Expr.variable("a", .bool)
        let b = Expr.variable("b", .bool)
        let c = Expr.variable("c", .bool)
        // formula = (a and b) or c
        let formula = Expr.or([.and([a, b]), c])
        let cnf = tseitin.transform(formula)

        runner.expectTrue(cnf.numVariables >= 3)
        runner.expectTrue(!cnf.clauses.isEmpty)
    }
}

runner.suite("AxiomAST And-Inverter Graph (AIG) Synthesizer") {
    runner.test("Structural hashing (strashing) node reuse") {
        let aig = AIGGraph()
        let a = aig.createVariable(name: "a")
        let b = aig.createVariable(name: "b")

        let gate1 = aig.and(a, b)
        let gate2 = aig.and(b, a) // reversed order should resolve to same node!
        runner.expectEqual(gate1, gate2)
        runner.expectEqual(aig.nodeCount, 3) // 2 variables + 1 unique AND node
    }

    runner.test("Full adder logic synthesis") {
        let aig = AIGGraph()
        let a = aig.createVariable(name: "a")
        let b = aig.createVariable(name: "b")
        let cin = aig.createVariable(name: "cin")

        let (sum, cout) = aig.fullAdder(bitA: a, bitB: b, carryIn: cin)
        runner.expectNotEqual(sum, cout)

        let (clauses, numVars) = aig.toCNF(outputs: [sum, cout])
        runner.expectTrue(numVars > 3)
        runner.expectTrue(!clauses.isEmpty)
    }
}

runner.suite("AxiomAST Serialization and Pretty Printing") {
    runner.test("SMT-LIB and Infix formatters") {
        let x = Expr.variable("x", .int)
        let y = Expr.variable("y", .int)
        let formula = Expr.le(Expr.add([x, Expr.mul([.int(2), y])]), .int(10))

        let smtPrinter = ASTPrinter(style: .smtlib)
        runner.expectEqual(smtPrinter.printExpr(formula), "(<= (+ x (* 2 y)) 10)")

        let infixPrinter = ASTPrinter(style: .infix)
        runner.expectEqual(infixPrinter.printExpr(formula), "x + 2 * y ≤ 10")
    }
}

runner.reportAndExit()
