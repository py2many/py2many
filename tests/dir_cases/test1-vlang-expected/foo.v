@[translated]
module main

import bar { bar1 }
import baz { baz1 }

fn main() {
	x := bar1()
	y := baz1()
	assert x == 0
	assert y == 'foo'
}
