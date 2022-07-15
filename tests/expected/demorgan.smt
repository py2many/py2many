
(declare-const a Bool)
(declare-const b Bool)


(define-fun demorgan ()  Bool
  (= (and a b) (not (or (not a) (not b)))))


(assert demorgan)
(check-sat)
(get-value (a b))
