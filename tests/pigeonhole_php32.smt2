; Pigeonhole Principle PHP(3, 2): 3 pigeons into 2 holes (UNSAT)
(set-logic QF_UF)

(declare-const p1_h1 Bool)
(declare-const p1_h2 Bool)
(declare-const p2_h1 Bool)
(declare-const p2_h2 Bool)
(declare-const p3_h1 Bool)
(declare-const p3_h2 Bool)

; Every pigeon must be in at least one hole
(assert (or p1_h1 p1_h2))
(assert (or p2_h1 p2_h2))
(assert (or p3_h1 p3_h2))

; No two pigeons can be in hole 1
(assert (not (and p1_h1 p2_h1)))
(assert (not (and p1_h1 p3_h1)))
(assert (not (and p2_h1 p3_h1)))

; No two pigeons can be in hole 2
(assert (not (and p1_h2 p2_h2)))
(assert (not (and p1_h2 p3_h2)))
(assert (not (and p2_h2 p3_h2)))

(check-sat)
(exit)
