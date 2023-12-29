@[translated]
module main

fn fib(i int) int {
	if i == 0 || i == 1 {
		return 1
	}

	return fib((i - 1)) + fib((i - 2))
}

fn main() {
	println((fib(5)).str())
}
