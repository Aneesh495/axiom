# Axiom: High-Performance Formal Verification Kernel & SMT Solver

Axiom is an industrial-grade formal verification kernel, SMT (Satisfiability Modulo Theories) decision engine, and program verifier written in Swift. It combines modern DPLL(T)/CDCL(T) lazy constraint solving, Nelson-Oppen multi-theory equality sharing, and Dijkstra weakest precondition semantics with C SIMD acceleration, Python differential testing against Z3, and an interactive HTML5/Canvas proof DAG visualizer.

```
      ___      _  _ _     ___  ___  __  __
     / _ \    \ \/ (_)___| _ \/ _ \|  \/  |
    / /_\ \    >  <| / _ \   / (_) | |\/| |
   /_/   \_\  /_/\_\_\___/_|_\\___/|_|  |_|
   Formal Verification Kernel & SMT Solver
```

[![Swift](https://img.shields.io/badge/Swift-6.0-orange.svg)](https://swift.org)
[![Platform](https://img.shields.io/badge/Platform-macOS%20%7C%20Linux-blue.svg)](https://apple.com)
[![License](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Tests](https://img.shields.io/badge/Tests-77%20Passed-brightgreen.svg)]()

---

## Key Capabilities

* **CDCL Propositional Core (`AxiomSAT`)**: Two-Watched-Literal (2WL) unit propagation, 1-UIP conflict analysis with asserting clauses, recursive clause minimization, VSIDS exponential decay activity heuristics, and Luby restart schedules.
* **First-Order Theory Solvers (`AxiomTheories`)**:
  * **EUF**: Dynamic congruence closure over E-graphs with proof forests.
  * **QF_LRA**: Dual Simplex over exact arbitrary-precision `Rational` numbers with Bland's cycling prevention and Farkas certificate generation.
  * **QF_LIA**: Branch-and-bound integer relaxation, Gomory cuts, and Bezout Diophantine GCD infeasibility refutation.
  * **QF_BV**: Word-level simplification, bit-blasting, and AIG logic circuit synthesis.
  * **QF_AX**: McCarthy arrays enforcing ROW1, ROW2, and extensionality axioms via reduction to EUF.
* **Cooperating SMT Engine (`AxiomSMT`)**: Nelson-Oppen equality sharing fixed-point loop, Delayed Theory Combination (DTC), Unsat Core extraction via assumption tracking, and Craig Interpolation.
* **Program Verification Engine (`AxiomVerify`)**:
  * Dijkstra Weakest Precondition (WP) predicate transformer calculus.
  * Bounded Model Checking (BMC) with loop unwinding and SSA path compilation.
  * Houdini inductive loop invariant synthesis.
  * Owicki-Gries concurrent thread safety and mutual exclusion verification.
* **SIMD Hardware Acceleration (`CAxiomKernel`)**:
  * AVX2 (256-bit) and ARM NEON (128-bit) vectorized popcount reductions.
  * Vectorized bitset AND/OR operations and dot-product acceleration.
* **Z3 Differential Testing (`python/`)**:
  * Randomized SMT-LIB 2.6 grammar fuzzer (`smtlib_generator.py`).
  * Cross-validation harness comparing Axiom against Z3 (`differential_tester.py`).
* **Interactive Proof DAG Visualizer (`web/`)**:
  * Canvas-rendered proof resolution trees, 1-UIP conflict cuts, and live SMT-LIB editor.

---

## Architecture Diagram

```
+-----------------------------------------------------------------------------+
|                                Axiom Engine                                 |
+-----------------------------------------------------------------------------+
                                       |
                   +-------------------+-------------------+
                   |                                       |
                   v                                       v
        +---------------------+                 +---------------------+
        |  AxiomVerify / BMC  |                 |      SMT-LIB 2.6    |
        | Program Verifier    |                 | Parser & CLI REPL   |
        +---------------------+                 +---------------------+
                   |                                       |
                   | Proof Obligations                     | AST Exprs
                   v                                       v
        +-------------------------------------------------------------+
        |                 AxiomAST Expression Pipeline                 |
        |  * Immutable DAG nodes with Type-Safe Sort System           |
        |  * Simplifier & Constant Folder (rewrites, idempotent rules) |
        |  * Plaisted-Greenbaum Polarity-Aware Tseitin Transformation  |
        |  * And-Inverter Graph (AIG) Structural Synthesizer           |
        +-------------------------------------------------------------+
                                       |
                                       v
        +-------------------------------------------------------------+
        |                  AxiomSMT / CDCL(T) Core                    |
        |  * Online Nelson-Oppen Purified Theory Dispatcher            |
        |  * Delayed Theory Combination (DTC) Splitter                |
        |  * Unsat Core Extraction (Assumption-Tracked Minimization)   |
        |  * Craig Interpolant Generator via Resolution Refutations    |
        +-------------------------------------------------------------+
                   |                                       |
      Boolean CNF  |                          Theory Lits  |
                   v                                       v
        +---------------------+                 +---------------------+
        |      AxiomSAT       |                 |    AxiomTheories    |
        |  * 2WL BCP Engine   | <==== Lemmas ===|  * EUF (E-graph)    |
        |  * 1-UIP Conflict   |                 |  * QF_LRA (Simplex) |
        |  * VSIDS Heuristics | === Decisions =>|  * QF_LIA (Cutting) |
        |  * DRAT Proofs      |                 |  * QF_BV (Bit-Blast)|
        +---------------------+                 |  * QF_AX (McCarthy) |
                   |                            +---------------------+
                   | SIMD Vector Bitset                    |
                   v                                       v
        +-------------------------------------------------------------+
        |                 CAxiomKernel (C99 / SIMD)                   |
        |  * AVX2 (256-bit) & ARM NEON (128-bit) Hardware Acceleration|
        |  * 64-bit Popcount Vector Reduction, Fast AND/OR Bitsets    |
        |  * SIMD Dot Product over Rational Tableau Basis             |
        +-------------------------------------------------------------+
```

---

## Repository Structure

```
.
├── Package.swift               # Swift Package Manager manifest
├── Sources/
│   ├── CAxiomKernel/           # C SIMD vector kernels (AVX2 / ARM NEON)
│   ├── AxiomCore/              # BigInt, Rational, BitVector, Union-Find, BitSet
│   ├── AxiomAST/               # Sorts, Expression AST, Simplifier, Tseitin, AIG
│   ├── AxiomSAT/               # CDCL SAT Solver, 2WL, 1-UIP, VSIDS, ProofLogger
│   ├── AxiomTheories/          # EUF, QF_LRA, QF_LIA, QF_BV, QF_AX Solvers
│   ├── AxiomSMT/               # Nelson-Oppen, DTC, UnsatCore, Interpolation, SMTSolver
│   ├── AxiomParser/            # SMT-LIB 2.6 Lexer, Parser, AST Builder
│   ├── AxiomVerify/            # Dijkstra VCGen, BMC, Houdini, Concurrency
│   ├── AxiomUI/                # DAG Visualizer JSON Serializer, Console Reporter
│   ├── AxiomCLI/               # SMT-LIB 2.6 REPL & Command-Line Driver
│   └── AxiomTestRunner/        # Unified Test Suite (77 test cases & regressions)
├── tests/                      # SMT-LIB 2.6 benchmark scripts (.smt2)
├── python/                     # Differential testing harness & Z3 cross-validator
├── web/                        # Interactive proof DAG visualizer (HTML5 Canvas)
└── docs/                       # Architecture, Formal Theory, and Verification guides
```

---

## Quickstart & Installation

### Prerequisites
* Swift 6.0+ (macOS Xcode Command Line Tools or Linux `swift-lang`)
* Python 3.9+ with `z3-solver` (for differential testing)

### Build the Complete Project
```bash
swift build -c release
```

### Run the Unified Test Suite
```bash
swift run AxiomTestRunner
```

Expected output:
```
=== Test Suite: BigInt Arithmetic and Logic ===
  ✓ Basic arithmetic operators
  ...
=== Test Suite: AxiomVerify Program Verification & Model Checking ===
  ✓ Dijkstra VCGen: Euclidean subtraction GCD verification
  ✓ Dijkstra VCGen: Counterexample generation for buggy swap
  ✓ Bounded Model Checking: Loop unwinding and assertion safety
  ✓ Houdini loop invariant candidate synthesis
  ✓ Owicki-Gries concurrent program safety and mutual exclusion
=== Test Suite: Axiom Kernel TDD Regression & Bug Reproduction Suite ===
  ✓ Regression BUG-001: Integer disequality feasibility over unconstrained tableau
  ✓ Regression BUG-002: Direct assertion of boolean false refutation
  ✓ Regression BUG-003: Recursive conjunction flattening into pure theory literals
  ✓ Regression BUG-004: Bounded model checker unwinding safety
  ✓ Regression BUG-005: CDCL 2WL watcher state consistency across restarts

----------------------------------------
Test Summary: 77 passed, 0 failed
ALL TESTS PASSED SMOOTHLY
```

---

## Command-Line Usage

### Interactive REPL
Launch the SMT-LIB 2.6 interactive read-eval-print loop:
```bash
swift run axiom
```

```
Axiom SMT Solver v1.0.0 (interactive mode)
Type '(exit)' to quit.
axiom> (declare-const x Int)
axiom> (declare-const y Int)
axiom> (assert (> x 0))
axiom> (assert (< y x))
axiom> (check-sat)
sat
axiom> (get-model)
(model
  (define-fun x () Int 2)
  (define-fun y () Int 1)
)
```

### File Solving & Model Extraction
```bash
swift run axiom tests/euclidean_gcd.smt2 --model
```

---

## Program Verification Examples

### Euclidean GCD Verification
Verifying that Dijkstra subtraction computes a strictly positive greatest common divisor:
```swift
import AxiomCore
import AxiomAST
import AxiomVerify

let vcgen = VCGen()
let a = Symbol("a"), b = Symbol("b"), x = Symbol("x"), y = Symbol("y"), res = Symbol("res")
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

let result = vcgen.verify(procedure: proc)
// Result: .verified(obligationsCount: 5)
```

---

## Python Differential Testing against Z3

Axiom includes an automated differential testing pipeline cross-validating results against Microsoft Z3:
```bash
pip install z3-solver
python3 python/differential_tester.py --iterations 100 --seed 42
```

---

## Interactive Web Proof Visualizer

Open `web/index.html` in any modern web browser to interactively explore:
* Resolution proof trees and 1-UIP conflict analysis cuts.
* E-graph equivalence classes and congruence edges.
* Live SMT-LIB 2.6 syntax editing and solving.

---

## License

MIT License. See [LICENSE](LICENSE) for details.
