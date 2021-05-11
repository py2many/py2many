package main

import (
	"fmt"
)

func Show() {
	var myfunc func(int, int) int = func(x int, y int) int { return (x + y) }
	fmt.Printf("%v\n", myfunc(1, 2))
}

func main() {
	Show()
}
