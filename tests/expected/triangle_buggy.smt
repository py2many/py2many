


(declare-datatypes () ((TriangleType EQUILATERAL ISOSCELES RIGHT ACUTE OBTUSE ILLEGAL)))
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)


(define-fun classify_triangle_correct ((a Int) (b Int) (c Int))  TriangleType
  (ite (and (= a b) (= b c))
       (assert (result None))
       (ite (or (= a b) (= b c) (= a c))
            (assert (result None))
            (let ((x y z) (sorted ((lambda ((i Int)) (ite (= i 0 1 2) a b c 0)) :init) true)))
            (ite (= (* x x) (+ (* y y) (* z z)))
                 (assert (result None))
                 (ite (< (* x x) (+ (* y y) (* z z)))
                      (assert (result None))
                      (assert (result None))))))
  result)


(define-fun classify_triangle-pre ((a Int) (b Int) (c Int))  TriangleType
  (and
    (> a 0)
    (> b 0)
    (> c 0)
    (< a (+ b c)))
  (ite (and (>= a b) (>= b c))
       (ite (or (= a c) (= b c))
            (ite (and (= a b) (= a c))
                 (assert (result None))
                 (assert (result None)))
            (ite (!= (* a a) (+ (* b b) (* c c)))
                 (ite (< (* a a) (+ (* b b) (* c c)))
                      (assert (result None))
                      (assert (result None)))
                 (assert (result None))))
       (assert (result None)))
  result)


(define-fun classify_triangle ((a Int) (b Int) (c Int))  TriangleType
  true
  (ite (and (>= a b) (>= b c))
       (ite (or (= a c) (= b c))
            (ite (and (= a b) (= a c))
                 (assert (result None))
                 (assert (result None)))
            (ite (!= (* a a) (+ (* b b) (* c c)))
                 (ite (< (* a a) (+ (* b b) (* c c)))
                      (assert (result None))
                      (assert (result None)))
                 (assert (result None))))
       (assert (result None)))
  result)


(assert (= (classify-triangle-correct a b c) (classify-triangle a b c)))
(check-sat)
