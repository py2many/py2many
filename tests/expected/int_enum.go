package main

import (
	"fmt"
)

type Colors int

const (
	RED   Colors = iota
	GREEN        = iota
	BLUE         = iota
)

type Permissions int

const (
	R Permissions = 1
	W             = 2
	X             = 16
)

func Show() {
	color_map := map[Colors]string{RED: "red", GREEN: "green", BLUE: "blue"}
	var a Colors = GREEN
	if a == GREEN {
		fmt.Printf("%v\n", "green")
	} else {
		fmt.Printf("%v\n", "Not green")
	}
	var b Permissions = R
	if b == R {
		fmt.Printf("%v\n", "R")
	} else {
		fmt.Printf("%v\n", "Not R")
	}
	if !(len(color_map) != 0) {
		panic("assert")
	}
}

func main() {
	Show()
}
