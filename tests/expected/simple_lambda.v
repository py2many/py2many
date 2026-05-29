@[translated]
module main

fn show() {
	f := fn (x int) int {
		return int(x) + 1
	}
	println((f(5)).str())
}

fn main() {
	show()
}
