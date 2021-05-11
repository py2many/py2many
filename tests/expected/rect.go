package main

import (
	"fmt"
)

// This file implements a rectangle class

type Rectangle struct {
	height int
	length int
}

func is_square(self Rectangle) bool {
	return self.height == self.length
}

func Show() {
	var r Rectangle = Rectangle{height: 1, length: 1}
	if !(is_square(r)) {
		panic("assert")
	}
	r = Rectangle{height: 1, length: 2}
	if !(!(is_square(r))) {
		panic("assert")
	}
	fmt.Printf("%v\n", r.height)
	fmt.Printf("%v\n", r.length)
}

func main() {
	Show()
}
