@[translated]
module main

fn compare_with_integer_variable() {
	i := 0
	mut s := 1
	if i {
		s = 2
	} else {
		s = 3
	}
	assert s == 3
}

fn use_zero_for_comparison() {
	i := 0
	mut s := 1
	if 0 {
		s = 2
	} else {
		s = 3
	}
	assert s == 3
}

fn main() {
	compare_with_integer_variable()
	use_zero_for_comparison()
	println('OK')
}
