; McCarthy Array Read-Over-Write Extensionality
(set-logic QF_AX)

(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const v Int)

; Store v at index i, then read back from i: select(store(a, i, v), i) == v
(declare-const a1 (Array Int Int))
(assert (= a1 (store a i v)))

; Assertion: select(a1, i) != v (UNSAT by ROW1 axiom)
(assert (not (= (select a1 i) v)))

(check-sat)
(exit)
