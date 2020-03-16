; Euclidean GCD Verification Condition in SMT-LIB 2.6
(set-logic QF_LIA)

(declare-const a Int)
(declare-const b Int)
(declare-const x Int)
(declare-const y Int)

; Precondition: a > 0 and b > 0
(assert (> a 0))
(assert (> b 0))

; Invariance: x > 0 and y > 0
(assert (> x 0))
(assert (> y 0))

; While loop condition: x != y
(assert (not (= x y)))

; Transition: if x > y then x' = x - y, y' = y
(declare-const x_prime Int)
(declare-const y_prime Int)

(assert (= x_prime (- x y)))
(assert (= y_prime y))
(assert (> x y))

; Verification condition: post invariant x' > 0 and y' > 0
(assert (not (and (> x_prime 0) (> y_prime 0))))

(check-sat)
(exit)
