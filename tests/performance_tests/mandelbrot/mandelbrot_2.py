def mandelbrot(limit, c):
    z = 0 + 0j
    for i in range(limit + 1):
        if abs(z) > 2:
            return i
        z = z * z + c
    return i + 1


if __name__ == "__main__":
    assert mandelbrot(1, 0.2 + 0.3j) == 2
    assert mandelbrot(5, 0.2 + 0.3j) == 6
    assert mandelbrot(6, 0.2 + 0.3j) == 7
    assert mandelbrot(10000, 1 + 0.3j) == 2
    assert mandelbrot(10000, 0.6 + 0.4j) == 4
