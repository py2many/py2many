package main

import (
	"fmt"
	"math"
)

func main() {
	var a int = int(math.Max(1, 2))
	fmt.Printf("%v\n", a)
	var b int = int(math.Min(1, 2))
	fmt.Printf("%v\n", b)
}
