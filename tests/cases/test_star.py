def sum_all(*nums):
    total = 0
    for n in nums:
        total += n
    return total

def main():
    # 4. Multiplication
    print('a' * 5)
    print([0] * 3)

    # 1. Splat in calls
    numbers = [1, 2, 3]
    print(sum_all(*numbers))

    # 2. List concatenation
    others = [4, 5]
    all_nums = [0, *numbers, *others, 6]
    print(all_nums)

    # 3. Extended unpacking
    data = [10, 20, 30, 40, 50]
    a, *rest, e = data
    print(a)
    print(rest)
    print(e)

if __name__ == "__main__":
    main()
