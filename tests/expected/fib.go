package main

import (
	"fmt"
)

func fib(i int) int {
	if i == 0 || i == 1 {
		return 1
	}
	return (fib((i - 1)) + fib((i - 2)))
}

func main() {
	rv := fib(5)
	fmt.Printf("%v\n", rv)
}
