package main

import (
	"fmt"
)

func Show() {
	fmt.Printf("%v\n", "b")
	fmt.Printf("%v %v\n", 2, "b")
	var a float64 = 2.1
	fmt.Printf("%v\n", a)
	var b float64 = 2.1
	fmt.Printf("%v\n", b)
}

func main() {
	Show()
}
