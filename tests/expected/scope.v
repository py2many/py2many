@[translated]
module main

const global_var = 10

fn test_global() {
	// global global_var  // V does not support global keyword
	global_var = 20
	println(global_var.str())
}

fn show() {
	test_global()
}

fn main() {
	show()
}
