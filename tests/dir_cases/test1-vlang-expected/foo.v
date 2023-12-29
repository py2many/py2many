@[translated]
module main

fn main() {
	x := bar1()
	y := baz1()
	assert x == 0
	assert y == 'foo'
}
