@[translated]
module main

import div72.vexc

fn show() {
	if C.try() {
		vexc.raise('Exception', 'foo')
		vexc.end_try()
	} else {
		match vexc.get_curr_exc().name {
			'Exception' {
				e := vexc.get_curr_exc()
				println('caught')
			}
			else {}
		}
	}
	println('Finally')
	if C.try() {
		vexc.raise('Exception', 'foo')
		vexc.end_try()
	} else {
		println('Got it')
	}
	if C.try() {
		vexc.raise('Exception', 'foo')
		vexc.end_try()
	} else {
		match vexc.get_curr_exc().name {
			'Exception' {
				e := vexc.get_curr_exc()
				assert e.str().contains('foo')
			}
			else {}
		}
	}
}

fn main() {
	show()
}
