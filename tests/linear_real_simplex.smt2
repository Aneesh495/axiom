; Linear Real Arithmetic Simplex Infeasibility
(set-logic QF_LRA)

(declare-const x Real)
(declare-const y Real)

; Convex polytope constraints
(assert (<= (+ x y) 2.0))
(assert (>= x 1.5))
(assert (>= y 1.0))

; Infeasible: x + y >= 2.5 > 2.0
(check-sat)
(exit)
