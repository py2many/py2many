@[translated]
module main

fn nested_containers() bool {
	CODES := {
		'KEY': [1, 3]
	}
	return 1 in CODES['KEY']
}

fn main() {
	if nested_containers() {
		println('OK')
	}
}
