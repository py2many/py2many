from py2many.smt import Array, check_sat, default_value, get_value
from py2many.smt import pre as smt_pre

cells: Array[int, int] = default_value(Array[int, int])

if smt_pre:
    pass
else:
    solved_board = [
        1,
        2,
        4,
        3,
        3,
        4,
        2,
        1,
        4,
        3,
        1,
        2,
        2,
        1,
        3,
        4,
    ]
    cells = solved_board


def cell(board: Array[int, int], row: int, col: int) -> int:
    return board[row * 4 + col]


def cell_value(value: int) -> bool:
    return value >= 1 and value <= 4


def unique4(a: int, b: int, c: int, d: int) -> bool:
    return a != b and a != c and a != d and b != c and b != d and c != d


def row_unique(board: Array[int, int], row: int) -> bool:
    return unique4(
        cell(board, row, 0),
        cell(board, row, 1),
        cell(board, row, 2),
        cell(board, row, 3),
    )


def col_unique(board: Array[int, int], col: int) -> bool:
    return unique4(
        cell(board, 0, col),
        cell(board, 1, col),
        cell(board, 2, col),
        cell(board, 3, col),
    )


def box_unique(board: Array[int, int], row: int, col: int) -> bool:
    return unique4(
        cell(board, row, col),
        cell(board, row, col + 1),
        cell(board, row + 1, col),
        cell(board, row + 1, col + 1),
    )


def row_values_valid(board: Array[int, int], row: int) -> bool:
    return (
        cell_value(cell(board, row, 0))
        and cell_value(cell(board, row, 1))
        and cell_value(cell(board, row, 2))
        and cell_value(cell(board, row, 3))
    )


def values_valid(board: Array[int, int]) -> bool:
    return (
        row_values_valid(board, 0)
        and row_values_valid(board, 1)
        and row_values_valid(board, 2)
        and row_values_valid(board, 3)
    )


def rows_unique(board: Array[int, int]) -> bool:
    return (
        row_unique(board, 0)
        and row_unique(board, 1)
        and row_unique(board, 2)
        and row_unique(board, 3)
    )


def cols_unique(board: Array[int, int]) -> bool:
    return (
        col_unique(board, 0)
        and col_unique(board, 1)
        and col_unique(board, 2)
        and col_unique(board, 3)
    )


def boxes_unique(board: Array[int, int]) -> bool:
    return (
        box_unique(board, 0, 0)
        and box_unique(board, 0, 2)
        and box_unique(board, 2, 0)
        and box_unique(board, 2, 2)
    )


def valid_board(board: Array[int, int]) -> bool:
    return (
        values_valid(board)
        and rows_unique(board)
        and cols_unique(board)
        and boxes_unique(board)
    )


assert valid_board(cells)
assert cell(cells, 0, 0) == 1
assert cell(cells, 0, 3) == 3
assert cell(cells, 1, 2) == 2

check_sat()
get_value((cells,))
