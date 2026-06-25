def sum_all(*nums: int) -> int:
    total: int = 0
    for n in nums:
        total += n
    return total


def main():
    # 4. Multiplication
    print("a" * 5)
    print([0] * 3)

    # 1. Splat in calls
    numbers: list[int] = [1, 2, 3]
    print(sum_all(*numbers))

    # 2. List concatenation
    others: list[int] = [4, 5]
    all_nums: list[int] = [0, *numbers, *others, 6]
    print(all_nums)

    # 3. Extended unpacking
    data: list[int] = [10, 20, 30, 40, 50]
    a: int
    rest: list[int]
    e: int
    a, *rest, e = data
    print(a)
    print(rest)
    print(e)


if __name__ == "__main__":
    main()
