@[translated]
module main

pub struct Foo {
}

fn (mut self Foo) bar() string {
	return 'a'
}

fn main() {
	f := Foo{}
	b := f.bar()
	println(b.str())
}
