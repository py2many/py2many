package main

import (
	"fmt"
)

func Test() int {
	var a []int = []int{1, 2, 3}
	return a[1]
}

func main() {
	var b int = Test()
	if !(b == 2) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}
