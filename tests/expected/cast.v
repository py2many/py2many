[translated]
module main

fn main_func() {
	a := i16(1)
	b := a
	println(b.str())
	c := i64(1)
	d := c
	println(d.str())
	e := u64(1)
	f := e
	println(f.str())
}

fn main() {
	main_func()
}
