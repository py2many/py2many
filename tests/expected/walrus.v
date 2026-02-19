@[translated]
module main

fn show() {
	n := [1, 2, 3].len
	if n > 2 {
		println(n.str())
	}

	mut i := 0
	for {
		x := (i * 2)
		if !(x < 10) {
			break
		}

		println(x.str())
		i += 1
	}
}

fn main() {
	show()
}
