package main

import (
	"fmt"
	"math"
)

func MainFunc() {
	var a int = int(math.Pow(float64(2), float64(4)))
	fmt.Printf("%v\n", a)
}

func main() {
	MainFunc()
}
