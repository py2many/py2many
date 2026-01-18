@[translated]
module main

import os

pub struct User {
pub mut:
	name string
}

fn new_user(name string) User {
	mut self := User{}
	self.name = name
	println(('Initializing ${self.name}').str())
	return self
}

fn (mut self User) free() {
	println(('Deleting ${self.name}').str())
}

fn (mut self User) say_hello() {
	println(('Hello, I am ${self.name}').str())
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
	println(('Post-init for ${self.name}, age ${self.age}').str())
}

fn main_func() {
	u := new_user('Alice')
	u.say_hello()
	du := new_datauser('Bob', 30)
	mut f := os.create('test.txt') or { panic(err) }
	defer { f.close() }
	f.write_string('Hello Vlang') or { panic(err) }
	if os.exists('test.txt') {
		os.rm('test.txt') or { panic(err) }
	}
}

fn main() {
	main_func()
}
