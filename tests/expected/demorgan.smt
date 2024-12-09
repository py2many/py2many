
(define-fun demorgan ((a Bool) (b Bool))  Bool
  (= (and a b) (not (or (not a) (not b)))))


(declare-const a Bool)
(declare-const b Bool)
(assert (not (demorgan a b)))
(check-sat)
