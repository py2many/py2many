package main

import (
	"fmt"
)

type Foo struct {
}

func (self Foo) bar() string {
	return "a"
}

func main() {
	var f Foo = Foo{}
	b := f.bar()
	fmt.Printf("%v\n", b)
}
