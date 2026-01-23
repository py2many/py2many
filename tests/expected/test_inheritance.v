@[translated]
module main

pub struct Parent {
pub mut:
	x int
}

fn new_parent(x int) Parent {
	mut self := Parent{}
	self.x = x
	return self
}

pub struct Child {
	Parent
pub mut:
	y int
}

fn new_child(x int, y int) Child {
	mut self := Child{}
	self.Parent = new_parent(x)
	self.y = y
	return self
}

fn main() {
	c := new_child(10, 20)
	println((c.x).str())
	println((c.y).str())
}
