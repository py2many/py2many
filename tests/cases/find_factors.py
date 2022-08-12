# From: https://book.pythontips.com/en/latest/for_-_else.html
# Modified example from the official Python documentation
def find_factors(n):
    for i in range(2, n):
        for j in range(2, i):
            if i % j == 0:
                print(i, 'equals', j, '*', i/j)
                break
        else:
            # loop fell through without finding a factor
            print(i, 'is a prime number')

if __name__ == "__main__":
    find_factors(100)