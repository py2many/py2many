package main

import (
	"fmt"
)

func Fib(i int) int {
	if i == 0 || i == 1 {
		return 1
	}
	return (Fib((i - 1)) + Fib((i - 2)))
}

func main() {
	fmt.Printf("%v\n", Fib(5))
}
