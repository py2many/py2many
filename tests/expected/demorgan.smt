
(declare-const a Bool)
(declare-const b Bool)


(define-fun demorgan ()  Bool
  (= (and a b) (not (or (not a) (not b)))))


(assert (not demorgan))
(check-sat)
