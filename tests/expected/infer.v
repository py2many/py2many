@[translated]
module main

fn foo() {
	a := 10
	b := a
	assert b == 10
	println(b.str())
}

fn main() {
	foo()
}
