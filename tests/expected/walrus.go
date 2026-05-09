package main

import (
	"fmt"
)

func Show() {
	n := len([]int{1, 2, 3})
	if n > 2 {
		fmt.Printf("%v\n", n)
	}
	var i int = 0
	for true {
		var x int = (i * 2)
		if !(x < 10) {
			break
		}
		fmt.Printf("%v\n", x)
		i += 1
	}
}

func main() {
	Show()
}
