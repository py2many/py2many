@[translated]
module main

fn for_with_break() {
	for i in 0 .. 4 {
		if i == 2 {
			break
		}

		println(i.str())
	}
}

fn for_with_continue() {
	for i in 0 .. 4 {
		if i == 2 {
			continue
		}

		println(i.str())
	}
}

fn for_with_else() {
	has_break := false
	for i in 0 .. 4 {
		println(i.str())
	}
	if has_break != true {
		println('OK')
	}
}

fn while_with_break() {
	mut i := 0
	for {
		if i == 2 {
			break
		}

		println(i.str())
		i += 1
	}
}

fn while_with_continue() {
	mut i := 0
	for i < 5 {
		i += 1
		if i == 2 {
			continue
		}

		println(i.str())
	}
}

fn main() {
	for_with_break()
	for_with_continue()
	for_with_else()
	while_with_break()
	while_with_continue()
}
