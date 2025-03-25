# Axiom System Architecture

Axiom is an industrial-grade formal verification kernel, SMT decision engine, and program verifier written in Swift, accelerated with SIMD bit-level vector kernels, verified with Python differential testing against Z3, and visualized via an interactive WebAssembly/HTML5 proof DAG viewer.

This document details the modular subsystem decomposition, data flow pipelines, memory ownership models, and concurrency guarantees that govern the Axiom verification engine.

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

## 1. Subsystem Decomposition

Axiom is engineered with strict layering: higher layers depend only on well-defined interfaces of lower layers, preventing cyclic couplings and maintaining clean test boundaries.

### 1.1 AxiomCore: High-Performance Verification Primitives
* **Arbitrary-Precision BigInt**: 64-bit limb radix arithmetic supporting multi-precision addition, subtraction, Karatsuba-inspired multiplication, Knuth Algorithm D quotient division, and binary Euclidean GCD.
* **Exact Rational Arithmetic**: Canonical irreducible fractions represented by coprime pairs `(numerator, denominator)` with zero denominator prevention and exact cross-multiplication comparisons.
* **BitVector Representations**: Arbitrary-width integer bitstrings with two's complement arithmetic, sign extension, zero extension, slice extraction, concatenation, bitwise operations, and arithmetic/logical shifts.
* **Arena Allocation**: Monotonic chunked arena allocators enabling $O(1)$ memory provisioning for ephemeral AST traversal without heap fragmentation.
* **Backtrackable Disjoint Sets (Union-Find)**: Forest data structure with path compression, union-by-rank, undo checkpoints for backtrackable theory states, and proof forest edge tracking for minimal conflict explanation.
* **Indexed Priority Queue**: Binary max-heap with $O(1)$ variable-to-index lookup supporting logarithmic key updates, powering the VSIDS decision heuristic.
* **Dense BitSet**: 64-bit word-packed bit array with popcount acceleration, set union, intersection, difference, and bit-level iterators.

### 1.2 AxiomAST: Expression Calculus & Normal Forms
* **Strongly-Typed Sort System**: Supports `.bool`, `.int`, `.real`, `.bitVector(width: Int)`, `.array(index: Sort, element: Sort)`, and `.uninterpreted(Symbol)`.
* **Structural Expression DAG**: Strongly-typed enum representations featuring boolean connectives, arithmetic operations, bitvector slices, and McCarthy array operations.
* **Simplifier & Constant Folder**: Evaluates constant subtrees, eliminates double negations, folds arithmetic identities ($x + 0 = x$, $x \times 0 = 0$), and reduces bit-vector identities ($x \oplus x = 0$, $x \ \& \ x = x$).
* **Plaisted-Greenbaum Tseitin Transformer**: Polarity-aware equisatisfiable CNF transformation generating at most $3n$ clauses for $n$ logical connectives, avoiding exponential formula explosion.
* **And-Inverter Graph (AIG) Engine**: Two-input AND nodes with inverted edges and structural hashing (strashing) for bit-blasted arithmetic circuits.

### 1.3 AxiomSAT: Modern CDCL Propositional Engine
* **Two-Watched-Literal (2WL) Scheme**: Watches exactly two non-false literals per clause, reducing literal evaluation overhead during backtracking to $O(1)$.
* **1-UIP Conflict Analysis**: First Unique Implication Point graph traversal producing asserting learned clauses with Literal Block Distance (LBD) metrics.
* **Recursive Clause Minimization**: Pruning self-subsumed and redundant literals from conflict clauses by recursively traversing implication reasons.
* **VSIDS Variable Selection**: Exponential decay activity scoring with periodic rescaling to prevent IEEE 754 overflow.
* **Luby Fast Restarts**: Non-monotonic restart sequence clearing search state while preserving learned clauses and saved literal polarities (phase saving).
* **DRAT Proof Logging**: Emits certified unsatisfiability proof certificates compatible with drat-trim.

### 1.4 AxiomTheories: First-Order Theory Solvers
* **Equality with Uninterpreted Functions (EUF)**: Dynamic congruence closure over an E-graph with function congruence rules and explanation forests.
* **Quantifier-Free Linear Real Arithmetic (QF_LRA)**: Dual Simplex algorithm over an exact Rational tableau with Bland's anti-cycling rule and Farkas infeasibility certificates.
* **Quantifier-Free Linear Integer Arithmetic (QF_LIA)**: Branch-and-bound integer relaxation coupled with Gomory cutting planes and Bezout Diophantine GCD infeasibility tests.
* **Quantifier-Free Bit-Vectors (QF_BV)**: Word-level simplifier with AIG bit-blasting and carry-ripple / shift-and-add arithmetic circuit synthesis.
* **Quantifier-Free Arrays (QF_AX)**: McCarthy array theory enforcing ROW1 (Read-Over-Write same index), ROW2 (Read-Over-Write distinct index), and extensionality axioms via reduction to EUF.

### 1.5 AxiomSMT: The Cooperating Decision Engine
* **CDCL(T) Lazy Search Loop**: SAT solver explores propositional assignments while theory solvers incrementally validate consistency and synthesize conflict lemmas.
* **Nelson-Oppen Equality Sharing**: Fixed-point propagation of equalities across stably infinite, disjoint theories over shared interface variables.
* **Delayed Theory Combination (DTC)**: Eliminates quadratic variable sharing overhead by turning interface equalities into propositional search choices.
* **Unsat Core Extractor**: Tracks activation assumptions during solving and computes minimal unsatisfiable sub-formulas via binary search and core pruning.
* **Craig Interpolation**: Synthesizes separating inductive invariants $I$ between formulas $A$ and $B$ where $A \implies I$ and $I \land B \implies \bot$.

### 1.6 AxiomVerify: Formal Program Verification
* **Dijkstra Weakest Precondition (WP) Calculus**: Backward predicate transformer computing verification conditions for assignment, branching, assert, assume, havoc, and heap operations.
* **Loop Invariant Verification**: Verifies initiation, invariance, and termination conditions over annotated while loops.
* **Bounded Model Checking (BMC)**: Unwinds arbitrary loop and recursion graphs up to user-specified bound $k$, compiles paths to Static Single Assignment (SSA) form, and checks assertion safety.
* **Houdini Candidate Synthesizer**: Inductive invariant synthesis selecting largest true inductive subset from a candidate predicate pool.
* **Owicki-Gries Concurrent Verifier**: Multi-threaded safety analysis verifying interference freedom and mutual exclusion over concurrent traces.

---

## 2. Memory Ownership and Allocation Strategy

To achieve deterministic memory consumption and eliminate garbage collection pauses, Axiom adheres to explicit memory architectures:

1. **Value-Semantic Immutability**: All core data types (`BigInt`, `Rational`, `BitVector`, `Expr`, `Sort`, `Literal`) are implemented as immutable Swift structs or enums with copy-on-write (COW) semantics.
2. **Arena Lifecycles**: Intermediate AST expressions created during Tseitin transformation and weakest precondition generation reside in scoped allocators, freed in a single operation upon solver scope exit.
3. **Contiguous Buffer Layouts**: SAT solver trails, watch lists, and simplex tableaux utilize flat 1D Swift arrays indexed by integer IDs, ensuring CPU cache locality and zero reference counting overhead during inner-loop BCP.
