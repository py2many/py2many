@[translated]
module main

fn show() {
	__unpack1 := [1, 2, 3, 4, 5]
	mut first := __unpack1[0]
	mut middle := __unpack1[1..__unpack1.len - 1]
	mut last := __unpack1.last()
	println(first.str() + ' ' + last.str())
}

fn main() {
	show()
}
