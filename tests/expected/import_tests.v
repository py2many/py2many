@[translated]
module main

fn test() int {
	a := [int(1), 2, 3]
	return a[1]
}

fn main() {
	b := test()
	assert b == 2
	println('OK')
}
