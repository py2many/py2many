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

// This file implements a rectangle class

pub struct Rectangle {
pub mut:
	height int
	length int
}

fn (mut self Rectangle) is_square() bool {
	return self.height == self.length
}

fn show() {
	mut r := new_rectangle(height: 1, length: 1)
	assert r.is_square()
	r = new_rectangle(height: 1, length: 2)
	assert !(r.is_square())
	println(any_to_string(r.height))
	println(any_to_string(r.length))
}

fn main() {
	show()
}
