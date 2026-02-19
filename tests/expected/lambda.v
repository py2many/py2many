@[translated]
module main

fn show() {
	myfunc := fn (x int, y int) int {
		return x + y
	}
	println((myfunc(1, 2)).str())
}

fn main() {
	show()
}
