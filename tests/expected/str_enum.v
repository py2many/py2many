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

struct Colors_t {
	red   string
	green string
	blue  string
}

const colors = Colors_t{
	red:   'red'
	green: 'green'
	blue:  'blue'
}

fn show() {
	color_map := {
		colors.red:   '1'
		colors.green: '2'
		colors.blue:  '3'
	}
	a := colors.green
	if a == colors.green {
		println('green')
	} else {
		println('Not green')
	}
	println(any_to_string(color_map.len))
}

fn main() {
	show()
}
