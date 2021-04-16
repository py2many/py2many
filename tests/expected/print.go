package main

import (
	"fmt"
)

func show() {
	fmt.Printf("%v\n", 2)
	fmt.Printf("%v\n", "b")
	fmt.Printf("%v %v\n", 2, "b")
}

func main() {
	show()
}
