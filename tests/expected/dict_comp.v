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
	squares := (fn () map[int]Any {
		mut result := map[int]Any{}
		for x in 0 .. 5 {
			result[x] = (x * x)
		}
		return result
	}())
	println(any_to_string(squares.len))
	evens := (fn () map[int]Any {
		mut result := map[int]Any{}
		for x in 0 .. 10 {
			if ((x as int) % 2) == 0 {
				result[x] = ((x as int) * 2)
			}
		}
		return result
	}())
	println(any_to_string(evens.len))
}

fn main() {
	show()
}
