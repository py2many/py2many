package main

import (
	"bar/bar1"
)
import (
	"baz/baz1"
)

func main() {
	x := bar1()
	y := baz1()
	if !(x == 0) {
		panic("assert")
	}
	if !(y == "foo") {
		panic("assert")
	}
}
