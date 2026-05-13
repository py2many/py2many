

(declare-const cells (Array Int Int))


(define-fun cell ((board (Array Int Int)) (row Int) (col Int))  Int
  (select board (+ (* row 4) col)))


(define-fun cell-value ((value Int))  Bool
  (and (>= value 1) (<= value 4)))


(define-fun unique4 ((a Int) (b Int) (c Int) (d Int))  Bool
  (and (not (= a b)) (not (= a c)) (not (= a d)) (not (= b c)) (not (= b d)) (not (= c d))))


(define-fun row-unique ((board (Array Int Int)) (row Int))  Bool
  (unique4 (cell board row 0) (cell board row 1) (cell board row 2) (cell board row 3)))


(define-fun col-unique ((board (Array Int Int)) (col Int))  Bool
  (unique4 (cell board 0 col) (cell board 1 col) (cell board 2 col) (cell board 3 col)))


(define-fun box-unique ((board (Array Int Int)) (row Int) (col Int))  Bool
  (unique4 (cell board row col) (cell board row (+ col 1)) (cell board (+ row 1) col) (cell board (+ row 1) (+ col 1))))


(define-fun row-values-valid ((board (Array Int Int)) (row Int))  Bool
  (and (cell-value (cell board row 0)) (cell-value (cell board row 1)) (cell-value (cell board row 2)) (cell-value (cell board row 3))))


(define-fun values-valid ((board (Array Int Int)))  Bool
  (and (row-values-valid board 0) (row-values-valid board 1) (row-values-valid board 2) (row-values-valid board 3)))


(define-fun rows-unique ((board (Array Int Int)))  Bool
  (and (row-unique board 0) (row-unique board 1) (row-unique board 2) (row-unique board 3)))


(define-fun cols-unique ((board (Array Int Int)))  Bool
  (and (col-unique board 0) (col-unique board 1) (col-unique board 2) (col-unique board 3)))


(define-fun boxes-unique ((board (Array Int Int)))  Bool
  (and (box-unique board 0 0) (box-unique board 0 2) (box-unique board 2 0) (box-unique board 2 2)))


(define-fun valid-board ((board (Array Int Int)))  Bool
  (and (values-valid board) (rows-unique board) (cols-unique board) (boxes-unique board)))


(assert (valid-board cells))
(assert (= (cell cells 0 0) 1))
(assert (= (cell cells 0 3) 3))
(assert (= (cell cells 1 2) 2))
(check-sat)
(get-value (cells))
