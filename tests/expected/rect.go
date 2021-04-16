package main

import (
	"fmt"
)

type Rectangle struct {
	height int
	length int
}

func is_square(self Rectangle) bool {
	return self.height == self.length
}

func show() {
	r := Rectangle(1, 1)
	if !(r.is_square()) {
		panic("assert")
	}
	r = Rectangle(1, 2)
	if !(!r.is_square()) {
		panic("assert")
	}
	h := r.height
	l := r.length
	fmt.Printf("%v\n", h)
	fmt.Printf("%v\n", l)
}

func main() {
	show()
}
