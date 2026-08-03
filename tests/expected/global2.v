@[translated]
module main

const code_0 = 0
const code_1 = 1
const code_a = 'a'
const code_b = 'b'
const l_b = [code_a]
const l_c = {
	code_b: code_0
}

fn main() {
	assert 'a' in l_b
	println('OK')
}
