# Axiom Formal Theory & Calculus Specification

This document presents the mathematical calculus, formal inference systems, and decision procedures implemented in the Axiom kernel.

---

## 1. Propositional Logic and the CDCL Calculus

The SAT decision engine implements the Conflict-Driven Clause Learning (CDCL) calculus with two-watched-literal propagation and 1-UIP conflict analysis.

### 1.1 State Transition Rules

A state is represented as $M \parallel F$, where $M$ is the trail of decided and propagated literals (annotated with decision level or reason clause), and $F$ is the clause database.

1. **Unit Propagation (BCP)**:
   $$\frac{M \parallel F \cup \{C \lor l\} \quad M \vDash \neg C \quad l \notin M}{M \, l^C \parallel F \cup \{C \lor l\}}$$

2. **Decide**:
   $$\frac{M \parallel F \quad l \text{ is undefined in } M}{M \, l^d \parallel F}$$

3. **Conflict Analysis (Resolution)**:
   $$\frac{M \parallel F \cup \{D \lor \neg p, \, C \lor p\} \quad M \vDash \neg D \land \neg C}{M \parallel F \cup \{D \lor C\}}$$

4. **1-UIP Backjump & Learn**:
   $$\frac{M \, l^d \, N \parallel F \cup \{C\} \quad \text{conflict } C \text{ at level } d \quad \text{1-UIP clause } C' \text{ backjump level } b < d}{M \, l'^{C'} \parallel F \cup \{C, C'\}}$$

5. **Restart**:
   $$\frac{M \parallel F}{\epsilon \parallel F}$$

---

## 2. Theory of Equality and Uninterpreted Functions (EUF)

Congruence closure is computed over an E-graph $G = (V, E)$ where vertices represent terms and directed hyper-edges represent function applications.

### 2.1 Inference Rules

1. **Reflexivity**:
   $$\frac{}{t \approx t}$$

2. **Symmetry**:
   $$\frac{t_1 \approx t_2}{t_2 \approx t_1}$$

3. **Transitivity**:
   $$\frac{t_1 \approx t_2 \quad t_2 \approx t_3}{t_1 \approx t_3}$$

4. **Congruence**:
   $$\frac{t_1 \approx u_1 \quad t_2 \approx u_2 \quad \dots \quad t_k \approx u_k}{f(t_1, \dots, t_k) \approx f(u_1, \dots, u_k)}$$

Conflict explanation is extracted by tracing paths in the proof forest maintained by the disjoint-set data structure.

---

## 3. Quantifier-Free Linear Real Arithmetic (QF_LRA)

Linear systems are expressed in canonical tableau form over exact rational numbers:
$$x_i = \sum_{j \in \mathcal{N}} a_{ij} x_j \quad (i \in \mathcal{B})$$
subject to bounds:
$$l_k \le x_k \le u_k \quad (k \in \mathcal{B} \cup \mathcal{N})$$

### 3.1 Dual Simplex Pivoting
When a basic variable $x_i$ violates its lower bound ($x_i < l_i$):
1. Select $x_i$ as the leaving variable.
2. Select a non-basic variable $x_j$ ($j \in \mathcal{N}$) as the entering variable such that $a_{ij} > 0$ and $x_j < u_j$ (or $a_{ij} < 0$ and $x_j > l_j$).
3. Apply the pivot operation:
   $$x_j = \frac{1}{a_{ij}} x_i - \sum_{k \in \mathcal{N} \setminus \{j\}} \frac{a_{ik}}{a_{ij}} x_k$$
   and update all basic variable definitions.
4. If no such entering variable exists, the row yields an infeasibility certificate $\sum_j \lambda_j a_{ij} \le 0$ with $\lambda_i > 0$ (Farkas' Lemma).

---

## 4. Quantifier-Free Linear Integer Arithmetic (QF_LIA)

Integer satisfiability combines continuous relaxation via Simplex with discrete branch-and-bound and Diophantine GCD checks.

### 4.1 Bezout GCD Infeasibility
For an integer equality $\sum_{i=1}^n a_i x_i = c$ where $a_i \in \mathbb{Z}$:
Let $g = \gcd(a_1, a_2, \dots, a_n)$. If $g \nmid c$, no integer solution exists.

### 4.2 Branch-and-Bound
If the continuous relaxation is feasible but a non-integer value $\alpha \notin \mathbb{Z}$ is assigned to integer variable $x$:
Split the search space into two branches:
$$x \le \lfloor \alpha \rfloor \quad \lor \quad x \ge \lceil \alpha \rceil$$

---

## 5. Nelson-Oppen Theory Combination

Let $T_1$ and $T_2$ be signature-disjoint, stably infinite first-order theories.
A formula $\phi$ is partitioned into purified conjunctions $\phi_1 \land \phi_2$ where $\phi_i$ contains only symbols from $T_i$ and auxiliary proxy variables.

### 5.1 Fixed-Point Equality Exchange
1. Assert purified literals to individual theory solvers $S_1$ and $S_2$.
2. For any shared variables $x, y$:
   If $S_i \vDash x \approx y$, broadcast $x \approx y$ to the other solver $S_{3-i}$.
3. Repeat until a contradiction is reported by either solver, or no new equality can be derived.
4. Completeness holds because $T_1$ and $T_2$ are convex and stably infinite over their shared sorts.
