@[translated]
module main

type AnyFn = fn (Any) Any

type Any = bool | int | i64 | f64 | string | []byte | voidptr
type List = []Any

pub struct MockFile {
pub mut:
	name   Any
	closed bool
}

fn new_mockfile[A](name A) MockFile {
	mut self := MockFile{}
	self.name = name
	self.closed = false
	return self
}

fn (mut self MockFile) __enter__() MockFile {
	println(('Opening ${self.name}').str())
	return self
}

fn (mut self MockFile) __exit__(exc_type Any, exc_val Any, exc_tb Any) bool {
	println(('Closing ${self.name}').str())
	self.closed = true
	return false
}

fn (mut self MockFile) read() string {
	return 'content'
}

fn show() {
	{
		mut __ctx1 := new_mockfile('test.txt')
		defer { __ctx1.__exit__(0, 0, 0) }
		mut f := __ctx1.__enter__()
		println((f.read()).str())
	}
}

fn main() {
	show()
}
