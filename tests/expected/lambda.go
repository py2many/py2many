package main

import (
	"fmt"
)

func show() {
	var myfunc None = func(x T, y T) int { (x + y) }
	fmt.Printf("%v\n", myfunc(1, 2))
}

func main() {
	show()
}
