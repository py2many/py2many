def fib(i: int) -> int:
    if i == 0 or i == 1:
        return 1
    return fib(i - 1) + fib(i - 2)


if __name__ == "__main__":
	# Using a variable to workaround
	# https://github.com/adsharma/py2many/issues/64
	rv = fib(5)
	print(rv)
