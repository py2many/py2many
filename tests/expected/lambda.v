@[translated]
module main

type AnyFn = fn (Any) Any

type Any = bool | int | i64 | f64 | string | []byte | voidptr
type List = []Any

fn any_to_string(value Any) string {
	return match value {
		string { value }
		bool, int, i64, f64 { value.str() }
		[]byte { value.bytestr() }
		voidptr { ptr_str(value) }
	}
}

fn show() {
	myfunc := fn (x int, y int) int {
		return x + y
	}
	println(any_to_string(myfunc(1, 2)))
}

fn main() {
	show()
}
