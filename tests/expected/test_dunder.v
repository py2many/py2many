@[translated]
module main

import os

type AnyFn = fn (Any) Any

type Any = bool | int | i64 | f64 | string | []byte | voidptr
type List = []Any

fn any_to_string(value Any) string {
	return match value {
		string { value }
		bool, int, i64, f64 { value.str() }
		[]byte { value.bytestr() }
		voidptr { ptr_str(value) }
	}
}

pub struct User {
pub mut:
	name string
}

fn new_user(name string) User {
	mut self := User{}
	self.name = name
	println(('Initializing ${any_to_string(self.name)}').str())
	return self
}

fn (mut self User) free() {
	println(('Deleting ${any_to_string(self.name)}').str())
}

fn (mut self User) say_hello() {
	println(('Hello, I am ${any_to_string(self.name)}').str())
}

pub struct DataUser {
pub mut:
	name string
	age  int
}

fn new_datauser(name string, age int) DataUser {
	mut self := DataUser{}
	self.name = name
	self.age = age
	self.__post_init__()
	return self
}

fn (mut self DataUser) __post_init__() {
	println(('Post-init for ${any_to_string(self.name)}, age ${any_to_string(self.age)}').str())
}

fn main_func() {
	u := new_user('Alice')
	u.say_hello()
	du := new_datauser('Bob', 30)
	{
		mut f := os.create('test.txt') or { panic(err) }
		defer { f.close() }
		f.write_string('Hello Vlang') or { panic(err) }
	}
	if os.exists('test.txt') {
		os.rm('test.txt') or { panic(err) }
	}
}

fn main() {
	main_func()
}
