

(declare-const x Int)
(declare-const y Int)
(declare-const z Real)


(define-fun equation-pre ((x Int) (y Int))  Bool
  (and
    (> x 2)
    (< y 10)
    (= (+ x (* 2 y)) 7)))


(define-fun equation ((x Int) (y Int))  Bool

  true)


(define-fun fequation-pre ((z Real))  Bool
  (and
    (= (+ 9.8 (* (to_real 2) z)) (+ z 9.11))))


(define-fun fequation ((z Real))  Bool

  true)


(assert (and
          (equation-pre  x y)
          (equation x y)))


(assert (and
          (fequation-pre  z)
          (fequation z)))


(check-sat)
(get-value (x y z))
