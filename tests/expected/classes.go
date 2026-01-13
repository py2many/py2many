package main

import (
	"fmt"
)

type Foo struct {
}

func (self Foo) bar() int {
	return self.baz()
}

func (self Foo) baz() int {
	return 10
}

func main() {
	var f Foo = Foo{}
	b := f.bar()
	fmt.Printf("%v\n", b)
	if !(b == 10) {
		panic("assert")
	}
}
