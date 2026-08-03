@[translated]
module main

const code_0 = 0
const code_1 = 1
const l_a = [code_0, code_1]
const code_a = 'a'
const code_b = 'b'
const l_b = [code_a, code_b]

fn main() {
	for i in l_a {
		println(i.str())
	}
	for j in l_b {
		println('${j}')
	}
	if 'a' in ['a', 'b'] {
		println('OK')
	}
}
