package main

import (
	"fmt"
	"strings"
)

type MockFile struct {
	name   interface{}
	closed bool
}

func (self MockFile) __init__(name interface{}) {
	self.name = name
	self.closed = false
}

func (self MockFile) __enter__() interface{} {
	fmt.Printf("%v\n", strings.Join([]string{"Opening ", fmt.Sprintf("%v", self.name)}, ""))
	return self
}

func (self MockFile) __exit__(exc_type interface{}, exc_val interface{}, exc_tb interface{}) bool {
	fmt.Printf("%v\n", strings.Join([]string{"Closing ", fmt.Sprintf("%v", self.name)}, ""))
	self.closed = true
	return false
}

func (self MockFile) read() string {
	return "content"
}

func Show() {
	{
		var f MockFile = MockFile{name: "test.txt"}
		fmt.Printf("%v\n", f.read())
	}
}

func main() {
	Show()
}
