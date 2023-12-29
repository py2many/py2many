@[translated]
module main

pub struct Foo {
}

fn (self Foo) bar() string {
	return 'a'
}

fn main() {
	f := Foo{}
	b := f.bar()
	println(b.str())
}
