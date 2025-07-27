


(declare-datatypes () ((TriangleType EQUILATERAL ISOSCELES RIGHT ACUTE OBTUSE ILLEGAL)))
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)


(define-fun classify_triangle_correct ((a Int) (b Int) (c Int))  TriangleType
  (ite (and (= a b) (= b c))
       EQUILATERAL
       (ite (or (= a b) (= b c) (= a c))
            ISOSCELES
            (let ((x y z) (sorted ((lambda ((i Int)) (ite (= i 0 1 2) a b c 0)) :init) true)))
            (ite (= (* x x) (+ (* y y) (* z z)))
                 RIGHT
                 (ite (< (* x x) (+ (* y y) (* z z)))
                      ACUTE
                      OBTUSE)))))


(define-fun classify_triangle-pre ((a Int) (b Int) (c Int))  TriangleType
  (and
    (> a 0)
    (> b 0)
    (> c 0)
    (< a (+ b c))))


(define-fun classify_triangle ((a Int) (b Int) (c Int))  TriangleType

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


(assert (= (classify-triangle-correct a b c) (classify-triangle a b c)))
(check-sat)
