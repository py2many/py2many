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
	f := fn (x Any) Any {
		return (x as int) + 1
	}
	println(any_to_string(f(5)))
	nums := [1, 2, 3]
	result := nums.map(fn (x Any) Any {
		return (x as int) * 2
	})
	println(any_to_string(result.len))
}

fn main() {
	show()
}
