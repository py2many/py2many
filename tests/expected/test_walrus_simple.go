package main

import (
	"fmt"
)

func Show() {
	var x int = 5
	if x > 3 {
		fmt.Printf("%v\n", x)
	}
}

func main() {
	Show()
}
