package main

import (
	"fmt"
)

type Foo struct {
}

func bar(self Foo) int {
	return baz(self)
}

func baz(self Foo) int {
	return 10
}

func main() {
	var f Foo = Foo{}
	b := bar(f)
	fmt.Printf("%v\n", b)
	if !(b == 10) {
		panic("assert")
	}
}
