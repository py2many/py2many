@[translated]
module main

// This file implements a rectangle class

pub struct Rectangle {
pub mut:
	height int
	length int
}

fn (self Rectangle) is_square() bool {
	return self.height == self.length
}

fn show() {
	mut r := Rectangle{
		height: 1
		length: 1
	}
	assert r.is_square()
	r = Rectangle{
		height: 1
		length: 2
	}
	assert !(r.is_square())
	println((r.height).str())
	println((r.length).str())
}

fn main() {
	show()
}
