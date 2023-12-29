@[translated]
module main

fn main_func() {
	mut ands := []bool{}
	mut ors := []bool{}
	mut xors := []bool{}
	for a in [false, true] {
		for b in [false, true] {
			ands << (a && b)
			ors << (a || b)
			xors << (a != b)
		}
	}
	assert ands == [false, false, false, true]
	assert ors == [false, true, true, true]
	assert xors == [false, true, true, false]
	println('OK')
}

fn main() {
	main_func()
}
