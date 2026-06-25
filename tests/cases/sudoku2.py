#!/usr/bin/env python3

from typing import List

from py2many.smt import check


def cell(board: List[int], row: int, col: int) -> int:
    return board[row * 4 + col]


def cell_value(value: int) -> bool:
    return value >= 1 and value <= 4


def unique4(a: int, b: int, c: int, d: int) -> bool:
    return a != b and a != c and a != d and b != c and b != d and c != d


def row_unique(board: List[int], row: int) -> bool:
    return unique4(
        cell(board, row, 0),
        cell(board, row, 1),
        cell(board, row, 2),
        cell(board, row, 3),
    )


def col_unique(board: List[int], col: int) -> bool:
    return unique4(
        cell(board, 0, col),
        cell(board, 1, col),
        cell(board, 2, col),
        cell(board, 3, col),
    )


def values_valid(board: List[int]) -> bool:
    return (
        cell_value(cell(board, 0, 0))
        and cell_value(cell(board, 1, 1))
        and cell_value(cell(board, 2, 2))
        and cell_value(cell(board, 3, 3))
    )


def valid_board(board: List[int]) -> bool:
    return (
        values_valid(board)
        and row_unique(board, 0)
        and row_unique(board, 1)
        and col_unique(board, 0)
        and col_unique(board, 1)
    )


def main():
    board = [1, 2, 4, 3, 3, 4, 2, 1, 4, 3, 1, 2, 2, 1, 3, 4]
    check(valid_board(board))
    print("valid")


if __name__ == "__main__":
    main()
