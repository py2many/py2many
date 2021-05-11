package main

import (
	"fmt"
)

func Foo() {
	var a int = 10
	var b int = a
	if !(b == 10) {
		panic("assert")
	}
	fmt.Printf("%v\n", b)
}

func main() {
	Foo()
}
