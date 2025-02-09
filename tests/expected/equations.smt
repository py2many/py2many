
(declare-const x Int)
(declare-const y Int)


(define-fun equation-pre ((x Int) (y Int))  Bool
  (and
    (> x 2)
    (< y 10)
    (= (+ x (* 2 y)) 7)))


(define-fun equation ((x Int) (y Int))  Bool
  true)


(assert (and
          (equation-pre  x y)
          (equation x y)))


(check-sat)
(get-value (x y))
