import Foundation
import AxiomCore
import AxiomAST
import AxiomSAT
import AxiomTheories
import AxiomSMT
import AxiomParser
import AxiomVerify

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

runner.suite("AxiomSAT CDCL Solver & Verification Benchmarks") {
    runner.test("Basic satisfiable and unsatisfiable CNF instances") {
        let solver1 = SATSolver()
        let x1 = Literal(variable: 0, isNegated: false)
        let x2 = Literal(variable: 1, isNegated: false)

        // (x1 or x2) and (~x1 or x2)
        solver1.addClause([x1, x2])
        solver1.addClause([~x1, x2])
        let res1 = solver1.solve()
        runner.expectEqual(res1, .sat)
        runner.expectEqual(solver1.modelValue(for: 1), true)

        let solver2 = SATSolver()
        // (x1) and (~x1) -> UNSAT
        solver2.addClause([x1])
        solver2.addClause([~x1])
        let res2 = solver2.solve()
        runner.expectEqual(res2, .unsat)
    }

    runner.test("Pigeonhole Principle PHP(4, 3) Provable UNSAT") {
        let solver = SATSolver()
        let pigeons = 4
        let holes = 3

        func pVar(_ p: Int, _ h: Int) -> Literal {
            return Literal(variable: Int32(p * holes + h), isNegated: false)
        }

        // Each pigeon must be in at least one hole: clause (p_i1 or p_i2 or ... or p_im)
        for p in 0..<pigeons {
            var clause: [Literal] = []
            for h in 0..<holes {
                clause.append(pVar(p, h))
            }
            solver.addClause(clause)
        }

        // No two pigeons in the same hole: clause (~p_ih or ~p_jh)
        for h in 0..<holes {
            for p1 in 0..<pigeons {
                for p2 in (p1 + 1)..<pigeons {
                    solver.addClause([~pVar(p1, h), ~pVar(p2, h)])
                }
            }
        }

        let res = solver.solve()
        runner.expectEqual(res, .unsat)
        runner.expectTrue(solver.stats.conflicts > 0)
    }

    runner.test("4-Queens Puzzle Satisfiability & Placement Model") {
        let solver = SATSolver()
        let n = 4

        func qVar(_ r: Int, _ c: Int) -> Literal {
            return Literal(variable: Int32(r * n + c), isNegated: false)
        }

        // At least one queen per row
        for r in 0..<n {
            var clause: [Literal] = []
            for c in 0..<n {
                clause.append(qVar(r, c))
            }
            solver.addClause(clause)
        }

        // At most one queen per row
        for r in 0..<n {
            for c1 in 0..<n {
                for c2 in (c1 + 1)..<n {
                    solver.addClause([~qVar(r, c1), ~qVar(r, c2)])
                }
            }
        }

        // At most one queen per column
        for c in 0..<n {
            for r1 in 0..<n {
                for r2 in (r1 + 1)..<n {
                    solver.addClause([~qVar(r1, c), ~qVar(r2, c)])
                }
            }
        }

        // At most one queen per diagonal
        for r1 in 0..<n {
            for c1 in 0..<n {
                for r2 in (r1 + 1)..<n {
                    for c2 in 0..<n {
                        if Swift.abs(r1 - r2) == Swift.abs(c1 - c2) {
                            solver.addClause([~qVar(r1, c1), ~qVar(r2, c2)])
                        }
                    }
                }
            }
        }

        let res = solver.solve()
        runner.expectEqual(res, .sat)

        // Verify exactly 4 queens placed
        var queensPlaced = 0
        for r in 0..<n {
            for c in 0..<n {
                if solver.modelValue(for: qVar(r, c).variable) {
                    queensPlaced += 1
                }
            }
        }
        runner.expectEqual(queensPlaced, 4)
    }

    runner.test("Incremental solving with assumption literals") {
        let solver = SATSolver()
        let a = Literal(variable: 0, isNegated: false)
        let b = Literal(variable: 1, isNegated: false)

        // a or b
        solver.addClause([a, b])

        // Under assumption ~a: b must be true
        let res1 = solver.solve(assumptions: [~a])
        runner.expectEqual(res1, .sat)
        runner.expectEqual(solver.modelValue(for: b.variable), true)

        // Under assumption ~a and ~b: UNSAT
        let res2 = solver.solve(assumptions: [~a, ~b])
        runner.expectEqual(res2, .unsat)

        // Under no assumptions: SAT
        let res3 = solver.solve(assumptions: [])
        runner.expectEqual(res3, .sat)
    }
}

runner.suite("AxiomTheories EUF Congruence Closure & Explanations") {
    runner.test("Transitivity of equality in E-graph") {
        let euf = EUFSolver()
        let sortU = Sort.uninterpreted(name: "U", arity: 0)
        let a = Expr.variable(name: "a", sort: sortU)
        let b = Expr.variable(name: "b", sort: sortU)
        let c = Expr.variable(name: "c", sort: sortU)

        runner.expectEqual(euf.assertLiteral(.eq(a, b)), .consistent)
        runner.expectEqual(euf.assertLiteral(.eq(b, c)), .consistent)
        runner.expectTrue(euf.areEquivalent(a, c))
    }

    runner.test("Function congruence rule f(x) == f(y)") {
        let euf = EUFSolver()
        let sortU = Sort.uninterpreted(name: "U", arity: 0)
        let x = Expr.variable(name: "x", sort: sortU)
        let y = Expr.variable(name: "y", sort: sortU)
        let fx = Expr.apply(function: "f", arguments: [x], returnSort: sortU)
        let fy = Expr.apply(function: "f", arguments: [y], returnSort: sortU)

        euf.intern(term: fx)
        euf.intern(term: fy)

        runner.expectFalse(euf.areEquivalent(fx, fy))
        runner.expectEqual(euf.assertLiteral(.eq(x, y)), .consistent)
        runner.expectTrue(euf.areEquivalent(fx, fy))
    }

    runner.test("Disequality conflict refutation and proof explanation") {
        let euf = EUFSolver()
        let sortU = Sort.uninterpreted(name: "U", arity: 0)
        let a = Expr.variable(name: "a", sort: sortU)
        let b = Expr.variable(name: "b", sort: sortU)
        let c = Expr.variable(name: "c", sort: sortU)

        runner.expectEqual(euf.assertLiteral(.eq(a, b)), .consistent)
        runner.expectEqual(euf.assertLiteral(.eq(b, c)), .consistent)

        // Now assert a != c: should immediately detect conflict
        let conflictRes = euf.assertLiteral(.not(.eq(a, c)))
        if case let .conflict(explanation) = conflictRes {
            runner.expectTrue(explanation.contains(.eq(a, b)))
            runner.expectTrue(explanation.contains(.eq(b, c)))
            runner.expectTrue(explanation.contains(.not(.eq(a, c))))
        } else {
            runner.expectTrue(false, "Expected conflict for inconsistent EUF equalities and disequality")
        }
    }

    runner.test("Incremental backtracking and scope popping") {
        let euf = EUFSolver()
        let sortU = Sort.uninterpreted(name: "U", arity: 0)
        let p = Expr.variable(name: "p", sort: sortU)
        let q = Expr.variable(name: "q", sort: sortU)

        euf.pushScope()
        runner.expectEqual(euf.assertLiteral(.eq(p, q)), .consistent)
        runner.expectTrue(euf.areEquivalent(p, q))

        euf.popScope()
        runner.expectFalse(euf.areEquivalent(p, q))
    }
}

runner.suite("AxiomTheories QF_LRA Simplex & Farkas Certificates") {
    runner.test("Feasible 2D linear inequality polytope") {
        let lra = LRASolver()
        let x = Expr.variable(name: "x", sort: .real)
        let y = Expr.variable(name: "y", sort: .real)

        // x >= 0, y >= 0, x + y <= 4, 2x + y <= 5
        runner.expectEqual(lra.assertLiteral(.ge(x, .realConst(.zero))), .consistent)
        runner.expectEqual(lra.assertLiteral(.ge(y, .realConst(.zero))), .consistent)
        runner.expectEqual(lra.assertLiteral(.le(.add([x, y]), .realConst(Rational(4)))), .consistent)
        runner.expectEqual(lra.assertLiteral(.le(.add([.mul([.realConst(Rational(2)), x]), y]), .realConst(Rational(5)))), .consistent)

        let res = lra.checkConsistency()
        runner.expectEqual(res, .consistent)

        // Verify model satisfies constraints
        let xVal = lra.variableValue(x) ?? .zero
        let yVal = lra.variableValue(y) ?? .zero
        runner.expectTrue(xVal >= .zero)
        runner.expectTrue(yVal >= .zero)
        runner.expectTrue(xVal + yVal <= Rational(4))
        runner.expectTrue(Rational(2) * xVal + yVal <= Rational(5))
    }

    runner.test("Infeasible linear system with Farkas conflict refutation") {
        let lra = LRASolver()
        let x = Expr.variable(name: "x", sort: .real)
        let y = Expr.variable(name: "y", sort: .real)

        // x >= 2, y >= 1, x + y <= 2 (impossible since 2 + 1 = 3 > 2)
        let c1 = Expr.ge(x, .realConst(Rational(2)))
        let c2 = Expr.ge(y, .realConst(Rational(1)))
        let c3 = Expr.le(.add([x, y]), .realConst(Rational(2)))

        runner.expectEqual(lra.assertLiteral(c1), .consistent)
        runner.expectEqual(lra.assertLiteral(c2), .consistent)
        let res = lra.assertLiteral(c3)

        if case let .conflict(explanation) = res {
            runner.expectTrue(explanation.contains(c1))
            runner.expectTrue(explanation.contains(c2))
            runner.expectTrue(explanation.contains(c3))
        } else {
            runner.expectTrue(false, "Expected conflict for inconsistent linear bounds")
        }
    }

    runner.test("Bounds propagation across simplex tableau row") {
        let lra = LRASolver()
        let x = Expr.variable(name: "x", sort: .real)
        let y = Expr.variable(name: "y", sort: .real)
        let sum = Expr.variable(name: "s", sort: .real)

        // s = x + y, x >= 2, y >= 3 -> s >= 5
        let xBound = Expr.ge(x, .realConst(Rational(2)))
        let yBound = Expr.ge(y, .realConst(Rational(3)))
        let defRow = Expr.eq(sum, .add([x, y]))

        runner.expectEqual(lra.assertLiteral(defRow), .consistent)
        runner.expectEqual(lra.assertLiteral(xBound), .consistent)
        runner.expectEqual(lra.assertLiteral(yBound), .consistent)

        let deductions = lra.propagateDeductions()
        let hasPropagatedLower = deductions.contains { d in
            if case let .ge(term, .realConst(val)) = d.literal, term == sum {
                return val >= Rational(5)
            }
            return false
        }
        runner.expectTrue(hasPropagatedLower, "Expected deduced lower bound s >= 5")
    }

    runner.test("Incremental scoping and backtracking in LRA Simplex") {
        let lra = LRASolver()
        let x = Expr.variable(name: "x", sort: .real)

        runner.expectEqual(lra.assertLiteral(.ge(x, .realConst(.zero))), .consistent)

        lra.pushScope()
        runner.expectEqual(lra.assertLiteral(.ge(x, .realConst(Rational(10)))), .consistent)
        runner.expectTrue((lra.variableValue(x) ?? .zero) >= Rational(10))

        lra.popScope()
        // Now x <= 5 is consistent because x >= 10 was popped
        runner.expectEqual(lra.assertLiteral(.le(x, .realConst(Rational(5)))), .consistent)
        runner.expectEqual(lra.checkConsistency(), .consistent)
    }
}

runner.suite("AxiomTheories QF_LIA Integer Arithmetic & Diophantine Verification") {
    runner.test("Feasible linear integer system with exact integer solution") {
        let lia = LIASolver()
        let x = Expr.variable(name: "x", sort: .int)
        let y = Expr.variable(name: "y", sort: .int)

        // x >= 0, y >= 0, x + y == 3, 2x + y == 4 -> x = 1, y = 2
        runner.expectEqual(lia.assertLiteral(.ge(x, .intConst(0))), .consistent)
        runner.expectEqual(lia.assertLiteral(.ge(y, .intConst(0))), .consistent)
        runner.expectEqual(lia.assertLiteral(.eq(.add([x, y]), .intConst(3))), .consistent)
        runner.expectEqual(lia.assertLiteral(.eq(.add([.mul([.intConst(2), x]), y]), .intConst(4))), .consistent)

        let res = lia.checkConsistency()
        runner.expectEqual(res, .consistent)
        runner.expectEqual(lia.integerVariableValue(x), BigInt(1))
        runner.expectEqual(lia.integerVariableValue(y), BigInt(2))
    }

    runner.test("Continuous feasible but integer infeasible fractional gap") {
        let lia = LIASolver()
        let x = Expr.variable(name: "x", sort: .int)

        // 2x == 1 -> x = 1/2 (continuous solution exists, but no integer solution)
        let c = Expr.eq(.mul([.intConst(2), x]), .intConst(1))
        _ = lia.assertLiteral(c)
        let res = lia.checkConsistency()
        runner.expectEqual(res, .conflict(explanation: [c]))
    }

    runner.test("Diophantine equation GCD infeasibility refutation") {
        let lia = LIASolver()
        let x = Expr.variable(name: "x", sort: .int)
        let y = Expr.variable(name: "y", sort: .int)

        // 4x + 6y == 5 (gcd(4, 6) = 2 does not divide 5)
        let diophantineEq = Expr.eq(
            .add([.mul([.intConst(4), x]), .mul([.intConst(6), y])]),
            .intConst(5)
        )
        let res = lia.assertLiteral(diophantineEq)
        if case let .conflict(explanation) = res {
            runner.expectTrue(explanation.contains(diophantineEq))
        } else {
            runner.expectTrue(false, "Expected GCD conflict for 4x + 6y == 5")
        }
    }

    runner.test("Branch-and-Bound fractional splitting") {
        let lia = LIASolver()
        let x = Expr.variable(name: "x", sort: .int)

        // 10x <= 25 and x >= 3 (10 * 3 = 30 > 25 -> UNSAT)
        let c1 = Expr.le(.mul([.intConst(10), x]), .intConst(25))
        let c2 = Expr.ge(x, .intConst(3))

        _ = lia.assertLiteral(c1)
        _ = lia.assertLiteral(c2)
        let res = lia.checkConsistency()
        if case .conflict = res {
            // Correctly detected conflict
        } else {
            runner.expectTrue(false, "Expected conflict for 10x <= 25 and x >= 3")
        }
    }
}

runner.suite("AxiomTheories QF_BV Bit-Vector AIG Bit-Blasting & Arithmetic") {
    runner.test("Word-level constant evaluation and bitwise algebra") {
        let bv = BVSolver()
        let a = Expr.bvConst(BitVector(width: 8, value: 0xAA))
        let b = Expr.bvConst(BitVector(width: 8, value: 0x55))

        // 0xAA ^ 0x55 == 0xFF
        let xorEq = Expr.eq(.bvXor(a, b), .bvConst(BitVector(width: 8, value: 0xFF)))
        runner.expectEqual(bv.assertLiteral(xorEq), .consistent)

        // 10 + 20 == 30
        let addEq = Expr.eq(
            .bvAdd(.bvConst(BitVector(width: 8, value: 10)), .bvConst(BitVector(width: 8, value: 20))),
            .bvConst(BitVector(width: 8, value: 30))
        )
        runner.expectEqual(bv.assertLiteral(addEq), .consistent)

        let res = bv.checkConsistency()
        runner.expectEqual(res, .consistent)
    }

    runner.test("Bit-blasted 8-bit modular addition and variable assignment") {
        let bv = BVSolver()
        let x = Expr.variable(name: "x", sort: .bitVec(width: 8))
        let five = Expr.bvConst(BitVector(width: 8, value: 5))
        let twelve = Expr.bvConst(BitVector(width: 8, value: 12))

        // x + 5 == 12 -> x == 7
        let eq = Expr.eq(.bvAdd(x, five), twelve)
        runner.expectEqual(bv.assertLiteral(eq), .consistent)

        let res = bv.checkConsistency()
        runner.expectEqual(res, .consistent)
        if let xVal = bv.getValue(of: x) {
            runner.expectEqual(xVal, BitVector(width: 8, value: 7))
        } else {
            runner.expectTrue(false, "Expected model value for variable x")
        }
    }

    runner.test("Bit-blasted bitwise masking and bit extraction") {
        let bv = BVSolver()
        let x = Expr.variable(name: "x", sort: .bitVec(width: 8))

        // x & 0x0F == 0x0A
        let maskAnd = Expr.eq(
            .bvAnd(x, .bvConst(BitVector(width: 8, value: 0x0F))),
            .bvConst(BitVector(width: 8, value: 0x0A))
        )
        // x & 0xF0 == 0xB0
        let maskOr = Expr.eq(
            .bvAnd(x, .bvConst(BitVector(width: 8, value: 0xF0))),
            .bvConst(BitVector(width: 8, value: 0xB0))
        )

        runner.expectEqual(bv.assertLiteral(maskAnd), .consistent)
        runner.expectEqual(bv.assertLiteral(maskOr), .consistent)

        let res = bv.checkConsistency()
        runner.expectEqual(res, .consistent)
        if let xVal = bv.getValue(of: x) {
            runner.expectEqual(xVal, BitVector(width: 8, value: 0xBA))
        } else {
            runner.expectTrue(false, "Expected model value for variable x")
        }
    }

    runner.test("Unsigned comparison refutation & overflow detection") {
        let bv = BVSolver()
        let x = Expr.variable(name: "x", sort: .bitVec(width: 8))

        // x + 1 <_u x (satisfiable if and only if x == 255)
        let one = Expr.bvConst(BitVector(width: 8, value: 1))
        let overflowCond = Expr.bvULt(.bvAdd(x, one), x)

        runner.expectEqual(bv.assertLiteral(overflowCond), .consistent)
        let res = bv.checkConsistency()
        runner.expectEqual(res, .consistent)

        if let xVal = bv.getValue(of: x) {
            runner.expectEqual(xVal, BitVector(width: 8, value: 255))
        } else {
            runner.expectTrue(false, "Expected model value for variable x on overflow")
        }
    }

    runner.test("Shift-and-add multiplication synthesis") {
        let bv = BVSolver()
        let x = Expr.variable(name: "x", sort: .bitVec(width: 8))
        let y = Expr.variable(name: "y", sort: .bitVec(width: 8))

        // x * y == 35, x > 1, y > 1 (factors of 35 are 5 and 7)
        let mulEq = Expr.eq(.bvMul(x, y), .bvConst(BitVector(width: 8, value: 35)))
        let xGt1 = Expr.bvULt(.bvConst(BitVector(width: 8, value: 1)), x)
        let yGt1 = Expr.bvULt(.bvConst(BitVector(width: 8, value: 1)), y)

        runner.expectEqual(bv.assertLiteral(mulEq), .consistent)
        runner.expectEqual(bv.assertLiteral(xGt1), .consistent)
        runner.expectEqual(bv.assertLiteral(yGt1), .consistent)

        let res = bv.checkConsistency()
        runner.expectEqual(res, .consistent)

        if let xVal = bv.getValue(of: x), let yVal = bv.getValue(of: y) {
            let xInt = xVal.words[0]
            let yInt = yVal.words[0]
            runner.expectEqual((xInt * yInt) & 0xFF, 35)
            runner.expectTrue(xInt > 1)
            runner.expectTrue(yInt > 1)
        } else {
            runner.expectTrue(false, "Expected model values for factors x and y")
        }
    }

    runner.test("Incremental backtracking and scope popping in BV solver") {
        let bv = BVSolver()
        let x = Expr.variable(name: "x", sort: .bitVec(width: 8))

        bv.pushScope()
        let c1 = Expr.eq(x, .bvConst(BitVector(width: 8, value: 42)))
        let c2 = Expr.eq(x, .bvConst(BitVector(width: 8, value: 43)))
        _ = bv.assertLiteral(c1)
        _ = bv.assertLiteral(c2)

        let resConflict = bv.checkConsistency()
        runner.expectEqual(resConflict, .conflict(explanation: [c1, c2]))

        bv.popScope()

        // After pop, asserting x == 43 should now be consistent
        _ = bv.assertLiteral(c2)
        let resConsistent = bv.checkConsistency()
        runner.expectEqual(resConsistent, .consistent)
        runner.expectEqual(bv.getValue(of: x), BitVector(width: 8, value: 43))
    }
}

runner.suite("AxiomTheories QF_AX McCarthy Arrays & Extensionality") {
    runner.test("McCarthy ROW1 axiom: same-index read-over-write") {
        let ax = ArraySolver()
        let arrSort = Sort.array(index: .int, element: .int)
        let a = Expr.variable(name: "a", sort: arrSort)
        let i = Expr.variable(name: "i", sort: .int)
        let v = Expr.variable(name: "v", sort: .int)

        // a1 = store(a, i, v)
        let a1 = Expr.store(array: a, index: i, value: v)
        // select(a1, i)
        let sel = Expr.select(array: a1, index: i)

        // Assert not(select(store(a, i, v), i) == v) -> should be UNSAT!
        let diseq = Expr.not(.eq(sel, v))
        _ = ax.assertLiteral(diseq)

        let res = ax.checkConsistency()
        if case .conflict = res {
            // Correctly proved ROW1 contradiction
        } else {
            runner.expectTrue(false, "Expected ROW1 conflict for select(store(a, i, v), i) != v")
        }
    }

    runner.test("McCarthy ROW2 axiom: distinct-index read-over-write") {
        let ax = ArraySolver()
        let arrSort = Sort.array(index: .int, element: .int)
        let a = Expr.variable(name: "a", sort: arrSort)
        let i = Expr.variable(name: "i", sort: .int)
        let j = Expr.variable(name: "j", sort: .int)
        let v = Expr.variable(name: "v", sort: .int)

        // i != j
        _ = ax.assertLiteral(.not(.eq(i, j)))

        // a1 = store(a, i, v)
        let a1 = Expr.store(array: a, index: i, value: v)
        let selA1 = Expr.select(array: a1, index: j)
        let selA = Expr.select(array: a, index: j)

        // Assert not(select(store(a, i, v), j) == select(a, j)) -> UNSAT!
        let diseq = Expr.not(.eq(selA1, selA))
        _ = ax.assertLiteral(diseq)

        let res = ax.checkConsistency()
        if case .conflict = res {
            // Correctly proved ROW2 contradiction under i != j
        } else {
            runner.expectTrue(false, "Expected ROW2 conflict under i != j")
        }
    }

    runner.test("Store chain overwriting at identical index") {
        let ax = ArraySolver()
        let arrSort = Sort.array(index: .int, element: .int)
        let a = Expr.variable(name: "a", sort: arrSort)
        let i = Expr.variable(name: "i", sort: .int)
        let v1 = Expr.variable(name: "v1", sort: .int)
        let v2 = Expr.variable(name: "v2", sort: .int)

        // a1 = store(a, i, v1)
        let a1 = Expr.store(array: a, index: i, value: v1)
        // a2 = store(a1, i, v2)
        let a2 = Expr.store(array: a1, index: i, value: v2)

        let sel = Expr.select(array: a2, index: i)

        // select(a2, i) == v2 should hold
        _ = ax.assertLiteral(.not(.eq(sel, v2)))
        let res = ax.checkConsistency()
        if case .conflict = res {
            // Overwrite correctly detected
        } else {
            runner.expectTrue(false, "Expected conflict when asserting select(store(store(a, i, v1), i, v2), i) != v2")
        }
    }

    runner.test("Array extensionality refutation for distinct arrays") {
        let ax = ArraySolver()
        let arrSort = Sort.array(index: .int, element: .int)
        let a = Expr.variable(name: "a", sort: arrSort)
        let b = Expr.variable(name: "b", sort: arrSort)

        // a != b and a == b -> immediate conflict
        _ = ax.assertLiteral(.not(.eq(a, b)))
        _ = ax.assertLiteral(.eq(a, b))

        let res = ax.checkConsistency()
        if case .conflict = res {
            // Refuted contradictory array equality
        } else {
            runner.expectTrue(false, "Expected extensionality conflict for a != b and a == b")
        }
    }

    runner.test("Incremental backtracking and scope restoration in Array solver") {
        let ax = ArraySolver()
        let arrSort = Sort.array(index: .int, element: .int)
        let a = Expr.variable(name: "a", sort: arrSort)
        let i = Expr.variable(name: "i", sort: .int)
        let v = Expr.variable(name: "v", sort: .int)

        let a1 = Expr.store(array: a, index: i, value: v)
        let sel = Expr.select(array: a1, index: i)

        ax.pushScope()
        _ = ax.assertLiteral(.not(.eq(sel, v)))
        let conflictRes = ax.checkConsistency()
        if case .conflict = conflictRes {
            // Expected
        } else {
            runner.expectTrue(false, "Expected conflict in scoped ROW assertion")
        }

        ax.popScope()

        // Asserting positive equality should be consistent
        _ = ax.assertLiteral(.eq(sel, v))
        let consistentRes = ax.checkConsistency()
        runner.expectEqual(consistentRes, .consistent)
    }
}

runner.suite("AxiomSMT & AxiomParser End-to-End Decision Engine") {
    runner.test("SMT-LIB 2.6 script parsing and execution") {
        let env = SMTLIBEnvironment()
        let script = """
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x 10.0))
        (assert (<= y 5.0))
        (assert (>= (+ x y) 15.0))
        (check-sat)
        (get-model)
        """
        do {
            let outputs = try env.execute(script: script)
            runner.expectTrue(outputs.contains("sat"))
        } catch {
            runner.expectTrue(false, "SMT-LIB execution failed: \(error)")
        }
    }

    runner.test("Unsat Core extraction and minimality") {
        let extractor = UnsatCoreExtractor()
        let x = Expr.variable(name: "x", sort: .int)
        let c1 = Expr.gt(x, .intConst(10))
        let c2 = Expr.lt(x, .intConst(5))
        let c3 = Expr.gt(x, .intConst(0)) // Redundant constraint

        let core = extractor.extractUnsatCore(from: [c1, c2, c3], minimize: true)
        if let core = core {
            runner.expectTrue(core.isMinimal)
            runner.expectEqual(core.expressions.count, 2)
            runner.expectTrue(core.expressions.contains(c1))
            runner.expectTrue(core.expressions.contains(c2))
            runner.expectFalse(core.expressions.contains(c3))
        } else {
            runner.expectTrue(false, "Expected minimal unsat core")
        }
    }

    runner.test("Craig Interpolation inductive barrier generation") {
        let interpolator = CraigInterpolator()
        let x = Expr.variable(name: "x", sort: .real)
        let a = Expr.le(x, .realConst(Rational(5)))
        let b = Expr.ge(x, .realConst(Rational(10)))

        let result = interpolator.interpolate(aFormula: a, bFormula: b)
        runner.expectTrue(result != nil)
        if let ip = result {
            runner.expectTrue(ip.sharedSymbols.contains(Symbol("x")))
        }
    }
}

runner.suite("AxiomVerify Program Verification & Model Checking") {
    runner.test("Dijkstra VCGen: Euclidean subtraction GCD verification") {
        let vcgen = VCGen()
        let a = Symbol("a")
        let b = Symbol("b")
        let x = Symbol("x")
        let y = Symbol("y")
        let res = Symbol("res")

        let aVar = Expr.variable(name: a, sort: .int)
        let bVar = Expr.variable(name: b, sort: .int)
        let xVar = Expr.variable(name: x, sort: .int)
        let yVar = Expr.variable(name: y, sort: .int)
        let resVar = Expr.variable(name: res, sort: .int)

        let body = Stmt.seq([
            .assign(variable: x, value: aVar),
            .assign(variable: y, value: bVar),
            .whileLoop(
                condition: .not(.eq(xVar, yVar)),
                invariant: .and([.gt(xVar, .intConst(0)), .gt(yVar, .intConst(0))]),
                body: .ifThenElse(
                    condition: .gt(xVar, yVar),
                    thenBranch: .assign(variable: x, value: .sub(xVar, yVar)),
                    elseBranch: .assign(variable: y, value: .sub(yVar, xVar))
                )
            ),
            .assign(variable: res, value: xVar)
        ])

        let proc = Procedure(
            name: Symbol("gcd"),
            parameters: [(name: a, sort: .int), (name: b, sort: .int)],
            returnSort: .int,
            requires: [.gt(aVar, .intConst(0)), .gt(bVar, .intConst(0))],
            ensures: [.gt(resVar, .intConst(0))],
            modifies: [x, y, res],
            body: body
        )

        let verifyRes = vcgen.verify(procedure: proc)
        if case let .verified(count) = verifyRes {
            runner.expectTrue(count >= 1)
        } else {
            runner.expectTrue(false, "Expected GCD procedure to verify, got: \(verifyRes)")
        }
    }

    runner.test("Dijkstra VCGen: Counterexample generation for buggy swap") {
        let vcgen = VCGen()
        let x = Symbol("x")
        let y = Symbol("y")
        let t = Symbol("t")

        let xVar = Expr.variable(name: x, sort: .int)
        let yVar = Expr.variable(name: y, sort: .int)

        // Buggy swap: t := x; x := y; y := x (should be y := t)
        let buggyBody = Stmt.seq([
            .assign(variable: t, value: xVar),
            .assign(variable: x, value: yVar),
            .assign(variable: y, value: xVar)
        ])

        let proc = Procedure(
            name: Symbol("buggySwap"),
            parameters: [(name: x, sort: .int), (name: y, sort: .int)],
            returnSort: nil,
            requires: [.eq(xVar, .intConst(1)), .eq(yVar, .intConst(2))],
            ensures: [.eq(xVar, .intConst(2)), .eq(yVar, .intConst(1))],
            modifies: [x, y, t],
            body: buggyBody
        )

        let verifyRes = vcgen.verify(procedure: proc)
        if case .counterexample = verifyRes {
            // Correctly caught bug!
        } else {
            runner.expectTrue(false, "Expected counterexample for buggy swap, got: \(verifyRes)")
        }
    }

    runner.test("Bounded Model Checking: Loop unwinding and assertion safety") {
        let bmc = BMC()
        let i = Symbol("i")
        let sum = Symbol("sum")

        let iVar = Expr.variable(name: i, sort: .int)
        let sumVar = Expr.variable(name: sum, sort: .int)

        // sum := 0; i := 0; while (i < 2) { sum := sum + 1; i := i + 1; }; assert(sum <= 2)
        let body = Stmt.seq([
            .assign(variable: sum, value: .intConst(0)),
            .assign(variable: i, value: .intConst(0)),
            .whileLoop(
                condition: .lt(iVar, .intConst(2)),
                invariant: nil,
                body: .seq([
                    .assign(variable: sum, value: .add([sumVar, .intConst(1)])),
                    .assign(variable: i, value: .add([iVar, .intConst(1)]))
                ])
            ),
            .assert(condition: .le(sumVar, .intConst(2)), message: "sum bound check")
        ])

        let proc = Procedure(
            name: Symbol("boundedLoop"),
            requires: [],
            ensures: [.le(sumVar, .intConst(2))],
            modifies: [i, sum],
            body: body
        )

        let res = bmc.check(procedure: proc, bound: 2)
        if case .safe = res {
            // Safe within bound!
        } else {
            runner.expectTrue(false, "Expected BMC to verify safety, got: \(res)")
        }
    }

    runner.test("Houdini loop invariant candidate synthesis") {
        let houdini = HoudiniSynthesizer()
        let i = Symbol("i")
        let iVar = Expr.variable(name: i, sort: .int)

        let loopBody = Stmt.assign(variable: i, value: .add([iVar, .intConst(1)]))
        let loopCond = Expr.lt(iVar, .intConst(10))
        let pre = Expr.eq(iVar, .intConst(0))

        let pool = [
            Expr.ge(iVar, .intConst(0)),
            Expr.le(iVar, .intConst(10)),
            Expr.eq(iVar, .intConst(0)), // Not inductive across body!
            Expr.eq(iVar, .intConst(5))  // Refuted initially!
        ]

        let invariant = houdini.synthesize(
            precondition: pre,
            loopCondition: loopCond,
            loopBody: loopBody,
            candidatePool: pool
        )

        runner.expectTrue(invariant != nil)
        if let inv = invariant {
            // Inductive invariant must retain i >= 0 in SMT-LIB prefix (>= i 0)
            runner.expectTrue(inv.description.contains(">="))
        }
    }

    runner.test("Owicki-Gries concurrent program safety and mutual exclusion") {
        let verifier = ConcurrencyVerifier()

        // Test Peterson-style mutual exclusion invariant:
        // Thread 1 in critical section: crit1 == 1
        // Thread 2 in critical section: crit2 == 1
        // Global invariant: not(crit1 == 1 and crit2 == 1)
        let crit1 = Expr.variable(name: "crit1", sort: .int)
        let crit2 = Expr.variable(name: "crit2", sort: .int)

        let t1Critical = Expr.eq(crit1, .intConst(1))
        let t2Critical = Expr.eq(crit2, .intConst(1))
        let globalInv = Expr.not(.and([t1Critical, t2Critical]))

        let mutexVerified = verifier.verifyMutualExclusion(
            thread1Critical: t1Critical,
            thread2Critical: t2Critical,
            globalInvariant: globalInv
        )
        runner.expectTrue(mutexVerified)
    }
}

runner.reportAndExit()



