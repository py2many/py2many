def mandelbrot(limit, c):
    z = 0+0j
    for i in range(limit+1):
        if abs(z) > 2:
            return i
        z = z*z + c
    return i+1

if __name__ == "__main__":
    assert mandelbrot(1000000, .2+.3j) == 1000001