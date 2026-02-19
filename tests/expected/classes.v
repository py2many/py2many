@[translated]
module main

pub struct Foo {
}

fn (mut self Foo) bar() int {
	return self.baz()
}

fn (mut self Foo) baz() int {
	return 10
}

fn main() {
	f := Foo{}
	b := f.bar()
	println(b.str())
	assert b == 10
}
