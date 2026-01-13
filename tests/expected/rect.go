package main

import (
	"fmt"
)

// This file implements a rectangle class

type Rectangle struct {
	height int
	length int
}

func (self Rectangle) is_square() bool {
	return self.height == self.length
}

func Show() {
	var r Rectangle = Rectangle{height: 1, length: 1}
	if !(r.is_square()) {
		panic("assert")
	}
	r = Rectangle{height: 1, length: 2}
	if !(!(r.is_square())) {
		panic("assert")
	}
	fmt.Printf("%v\n", r.height)
	fmt.Printf("%v\n", r.length)
}

func main() {
	Show()
}
