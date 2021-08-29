package main

import (
	"fmt"
	"math"
)

func DefaultBuiltins() {
	var a string = ""
	var b bool = false
	var c int = 0
	if !(a == "") {
		panic("assert")
	}
	if !(b == false) {
		panic("assert")
	}
	if !(c == 0) {
		panic("assert")
	}
}

func main() {
	var a int = int(math.Max(1, 2))
	fmt.Printf("%v\n", a)
	var b int = int(math.Min(1, 2))
	fmt.Printf("%v\n", b)
}
