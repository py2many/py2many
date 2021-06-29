fn show() {
	println('b')
	println((2).str() + ' ' + 'b')
	a := f32(2.1)
	println(a.str())
	b := 2.1
	println(b.str())
	c := true
	println((if c { 'True' } else { 'False' }).str())
}

fn main() {
	show()
}
