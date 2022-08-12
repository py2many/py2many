def binomial_coef(n: int, k: int):
    C = [[0 for x in range(k + 1)] for x in range(n + 1)]
    for i in range(n + 1):
        for j in range(min(i, k) + 1):
            if j == 0 or j == i:
                C[i][j] = 1
            else:
                C[i][j] = C[i - 1][j - 1] + C[i - 1][j]
    return C[n][k]


if __name__ == "__main__":
    assert binomial_coef(10, 6) == 210
    assert binomial_coef(20, 6) == 38760
    assert binomial_coef(4000, 6) == 5667585757783866000
