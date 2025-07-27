


(declare-datatypes () ((TriangleType EQUILATERAL ISOSCELES RIGHT ACUTE OBTUSE ILLEGAL)))
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)


(define-fun classify-triangle-correct ((a Int) (b Int) (c Int))  TriangleType
  (ite (and (= a b) (= b c))
       EQUILATERAL
       (ite (or (= a b) (= b c) (= a c))
            ISOSCELES
            (ite (and (>= a b) (>= a c))
                 (ite (= (* a a) (+ (* b b) (* c c)))
                      RIGHT
                      (ite (< (* a a) (+ (* b b) (* c c)))
                           ACUTE
                           OBTUSE))
                 (ite (and (>= b a) (>= b c))
                      (ite (= (* b b) (+ (* a a) (* c c)))
                           RIGHT
                           (ite (< (* b b) (+ (* a a) (* c c)))
                                ACUTE
                                OBTUSE))
                      (ite (= (* c c) (+ (* a a) (* b b)))
                           RIGHT
                           (ite (< (* c c) (+ (* a a) (* b b)))
                                ACUTE
                                OBTUSE)))))))


(define-fun classify-triangle-pre ((a Int) (b Int) (c Int)) Bool
  (and
    (> a 0)
    (> b 0)
    (> c 0)
    (< a (+ b c))))


(define-fun classify-triangle ((a Int) (b Int) (c Int))  TriangleType

  (ite (and (>= a b) (>= b c))
       (ite (or (= a c) (= b c))
            (ite (and (= a b) (= a c))
                 EQUILATERAL
                 ISOSCELES)
            (ite (not (= (* a a) (+ (* b b) (* c c))))
                 (ite (< (* a a) (+ (* b b) (* c c)))
                      ACUTE
                      OBTUSE)
                 RIGHT))
       ILLEGAL))


(assert (not (= (classify-triangle-correct a b c) (classify-triangle a b c))))
(check-sat)
(get-model)
