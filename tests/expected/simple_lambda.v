@[translated]
module main

type AnyFn = fn (Any) Any

type Any = bool | int | i64 | f64 | string | []byte | voidptr
type List = []Any

fn show() {
	f := fn (x Any) Any {
		return (x as int) + 1
	}
	println((f(5)).str())
}

fn main() {
	show()
}
