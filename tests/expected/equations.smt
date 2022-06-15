
(declare-const x Int)
(declare-const y Int)
(assert (> x 2))
(assert (< y 10))
(assert (= (+ x (* 2 y)) 7))
(check-sat)
(get-value (x y))
