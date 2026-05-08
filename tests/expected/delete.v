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
	my_list := [1, 2, 3, 4, 5]
	my_list.delete(2)
	println(any_to_string(my_list.len))
	my_dict := {
		'a': 1
		'b': 2
		'c': 3
	}
	my_dict.delete('b')
	println(any_to_string(my_dict.len))
}

fn main() {
	show()
}
