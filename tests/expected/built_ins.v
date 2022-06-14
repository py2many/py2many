[translated]
module main

import arrays

fn default_builtins() {
	a := ''
	b := false
	c := 0
	assert a == ''
	assert b == false
	assert c == 0
}

fn main() {
	a := arrays.max([1, 2]) or { panic('!') }
	println(a.str())
	b := arrays.min([1, 2]) or { panic('!') }
	println(b.str())
}
