@[translated]
module main

fn show() {
	a := 1
	b := if a in [2, 3] { 2 } else { 3 }
	println(b.str())
}

fn main() {
	show()
}
