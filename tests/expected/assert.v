@[translated]
module main

fn compare_assert(a int, b int) {
	assert a == b
	assert !(0 == 1)
}

fn main() {
	assert true
	assert !(false)
	compare_assert(1, 1)
	assert true
	assert true
	println('OK')
}
