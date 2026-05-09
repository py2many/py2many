package main

import (
	"fmt"
)

func Show() {
	f := func(x int) int { return (x + 1) }
	fmt.Printf("%v\n", f(5))
}

func main() {
	Show()
}
