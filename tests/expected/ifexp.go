package main

import (
	"fmt"
	"github.com/electrious/refutil"
)

func Show() {
	var a int = 1
	var b int
	if refutil.Contains([]int{2, 3}, a) {
		b = 2
	} else {
		b = 3
	}
	fmt.Printf("%v\n", b)
}

func main() {
	Show()
}
