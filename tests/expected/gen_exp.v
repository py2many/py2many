@[translated]
module main

fn show() {
	gen := (fn () []int {
		mut result := []int{}
		for it in 0 .. 5 {
			result << (it * it)
		}
		return result
	}())
	for val in gen {
		println(val.str())
	}
}

fn main() {
	show()
}
