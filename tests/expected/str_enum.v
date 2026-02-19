@[translated]
module main

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
	println((color_map.len).str())
}

fn main() {
	show()
}
