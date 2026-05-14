@[translated]
module main

fn nested_containers() bool {
	codes := {
		'KEY': [1, 3]
	}
	return 1 in codes['KEY']
}

fn main() {
	if nested_containers() {
		println('OK')
	}
}
