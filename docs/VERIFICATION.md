# Axiom Verification & Proof Engineering Guide

This document describes the formal verification techniques implemented in `AxiomVerify` for validating correctness, memory safety, and thread safety in software procedures.

---

## 1. Dijkstra Weakest Precondition (WP) Calculus

The predicate transformer $wp(S, Q)$ computes the weakest condition on the initial state of program $S$ such that execution terminates in a state satisfying postcondition $Q$.

### 1.1 Structural Transformer Rules

| Statement $S$ | Weakest Precondition $wp(S, Q)$ |
| :--- | :--- |
| `skip` | $Q$ |
| `assign(x, E)` | $Q[x \mapsto E]$ (Capture-avoiding substitution) |
| `seq(S1, S2)` | $wp(S_1, wp(S_2, Q))$ |
| `ifThenElse(C, S1, S2)` | $(C \implies wp(S_1, Q)) \land (\neg C \implies wp(S_2, Q))$ |
| `assert(C)` | $C \land Q$ |
| `assume(C)` | $C \implies Q$ |
| `havoc(x)` | $\forall x. \, Q$ (instantiated with fresh Skolem constant) |
| `load(dest, base, offset)` | $Q[\text{dest} \mapsto \text{select}(\text{HEAP}, \text{base} + \text{offset})]$ |
| `store(base, offset, val)` | $Q[\text{HEAP} \mapsto \text{store}(\text{HEAP}, \text{base} + \text{offset}, \text{val})]$ |
| `alloc(dest, size)` | $\text{freshPtr} > 0 \land Q[\text{dest} \mapsto \text{freshPtr}]$ |
| `free(ptr)` | $Q$ |

### 1.2 Loop Verification with Invariants

For a loop `while (C) invariant (I) body (S)` with postcondition $Q$:
Three proof obligations must be verified:
1. **Initiation**: $\text{Pre} \implies I$
2. **Consecution / Invariance**: $(I \land C) \implies wp(S, I)$
3. **Termination**: $(I \land \neg C) \implies Q$

A procedure is verified if and only if all proof obligations are valid (their refutations are unsatisfiable in SMT).

---

## 2. Bounded Model Checking (BMC)

Bounded Model Checking verifies safety properties up to a finite unwinding depth $k$.
1. Loops and recursion are unrolled $k$ times sequentially into bounded if-then-else statements.
2. The terminating iteration assumes the loop condition is false ($\neg C$).
3. The execution paths are translated into Static Single Assignment (SSA) form with phi-node join constraints.
4. Each assertion $A$ along path condition $P$ is checked for refutation:
   $$\text{Check Satisfiability of } P \land \neg A$$
   If SAT is found, the solver model provides a concrete counterexample trace.

---

## 3. Houdini Invariant Synthesis

The Houdini algorithm synthesizes inductive loop invariants from an annotated candidate pool $\mathcal{H} = \{h_1, h_2, \dots, h_m\}$:
1. Initialize candidate invariant $I = \bigwedge_{h \in \mathcal{H}} h$.
2. Check if $\text{Pre} \implies I$. Remove any candidate violated initially.
3. Check if $(I \land C) \implies wp(S, I)$. For any candidate $h_j$ violated after the loop body, remove $h_j$ from $I$.
4. Repeat until fixed point is reached.
5. If the remaining set is non-empty, it is guaranteed to be an inductive invariant.

---

## 4. Owicki-Gries Concurrency Verification

Given concurrent threads $T_1$ and $T_2$ operating on shared state:
1. Each thread has sequential pre/post assertions.
2. Interference freedom checks verify that no action of $T_2$ invalidates the local invariants of $T_1$, and vice-versa.
3. Mutual exclusion invariants (e.g. $\neg(\text{crit}_1 \land \text{crit}_2)$) are validated against all reachable inter-thread states.
