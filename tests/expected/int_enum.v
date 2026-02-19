@[translated]
module main

enum Colors {
	red
	green
	blue
}

enum Permissions {
	r = 1
	w = 2
	x = 16
}

fn show() {
	color_map := {
		Colors.red:   'red'
		Colors.green: 'green'
		Colors.blue:  'blue'
	}
	a := Colors.green
	if a == Colors.green {
		println('green')
	} else {
		println('Not green')
	}
	b := Permissions.r
	if b == Permissions.r {
		println('R')
	} else {
		println('Not R')
	}
	assert color_map.len != 0
}

fn main() {
	show()
}
