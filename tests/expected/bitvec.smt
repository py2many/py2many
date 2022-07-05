

(declare-const myu32 (_ BitVec 32))
(assert (= myu32 #x0000000a))
(check-sat)
(get-value (myu32))
