package main

import (
	"fmt"
)

func Show() {
	__tmp6_4 := []int{1, 2, 3, 4, 5}
	first := __tmp6_4[0]
	_ = first
	middle := __tmp6_4[1 : len(__tmp6_4)-1]
	_ = middle
	last := __tmp6_4[len(__tmp6_4)-1]
	_ = last
	fmt.Printf("%v %v\n", first, last)
}

func main() {
	Show()
}
