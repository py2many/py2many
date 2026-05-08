@[translated]
module main

fn show() {
	f := fn (x int) int {
		return (x as int) + 1
	}
	println((f(5)).str())
	nums := [1, 2, 3]
	result := nums.map(fn (x int) int {
		return (x as int) * 2
	})
	println((result.len).str())
}

fn main() {
	show()
}
