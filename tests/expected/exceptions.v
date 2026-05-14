@[translated]
module main

fn show() {
	{
		defer {
			println('Finally')
		}
		println('caught')
	}
	println('Got it')
	e := 'foo'
	assert e.str().contains('foo')
}

fn main() {
	show()
}
