@[translated]
module main

import os

fn main() {
	a := os.args
	cmd := a[0]
	if cmd == 'dart' {
	} else {
		assert cmd.contains('sys_argv')
	}
	if a.len > 1 {
		println('${a[1]}')
	} else {
		println('OK')
	}
}
