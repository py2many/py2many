@[translated]
module main

pub struct Foo {
}

fn (self Foo) bar() int {
	return self.baz()
}

fn (self Foo) baz() int {
	return 10
}

fn main() {
	f := Foo{}
	b := f.bar()
	println(b.str())
	assert b == 10
}
