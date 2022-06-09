# Assuming m >= n.
def bonacciseries(n: int, m: int) :
    a = [0] * m
    a[n - 1] = 1
    for i in range(n, m) :
        for j in range(i - n, i) :
            a[i] = a[i] + a[j]
    return a