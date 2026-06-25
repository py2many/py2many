set_option linter.unusedVariables false

def cell (board : List Nat) (row : Nat) (col : Nat) : Nat :=
  board[((row * 4) + col)]!

def cell_value (value : Nat) : Bool :=
  (value ≥ 1 && value ≤ 4)

def unique4 (a : Nat) (b : Nat) (c : Nat) (d : Nat) : Bool :=
  (a != b && a != c && a != d && b != c && b != d && c != d)

def row_unique (board : List Nat) (row : Nat) : Bool :=
  (unique4 (cell board row 0) (cell board row 1) (cell board row 2) (cell board row 3))

def col_unique (board : List Nat) (col : Nat) : Bool :=
  (unique4 (cell board 0 col) (cell board 1 col) (cell board 2 col) (cell board 3 col))

def values_valid (board : List Nat) : Bool :=
  ((cell_value (cell board 0 0)) && (cell_value (cell board 1 1)) && (cell_value (cell board 2 2)) &&
    (cell_value (cell board 3 3)))

def valid_board (board : List Nat) : Bool :=
  ((values_valid board) && (row_unique board 0) && (row_unique board 1) && (col_unique board 0) && (col_unique board 1))

def main_func : IO Unit := do
  let board := [1, 2, 4, 3, 3, 4, 2, 1, 4, 3, 1, 2, 2, 1, 3, 4]
  have _ : (valid_board board) = true := by native_decide
  IO.println "valid"

def main : IO Unit := do
  main_func
