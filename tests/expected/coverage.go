package main

import (
	"fmt"
	iter "github.com/hgfischer/go-iter"
)

func indexing() int {
	var sum int = 0
	var a []int = []int{}
	for _, i := range iter.NewIntSeq(iter.Start(0), iter.Stop(10)).All() {
		a = append(a, i)
		sum += a[i]
	}
	return sum
}

func show() {
	var a1 int = 10
	var a2 float64 = 2.1
	fmt.Printf("%v\n", a2)
	for _, i := range iter.NewIntSeq(iter.Start(0), iter.Stop(10)).All() {
		fmt.Printf("%v\n", i)
	}
	for _, i := range iter.NewIntSeq(iter.Start(0), iter.Stop(10), iter.Step(2)).All() {
		fmt.Printf("%v\n", i)
	}
	var a3 int = -(a1)
	var a4 int = (a3 + a1)
	fmt.Printf("%v\n", a4)
	var sum1 int = indexing()
	fmt.Printf("%v\n", sum1)
	var a5 []int = []int{1, 2, 3}
	fmt.Printf("%v\n", len(a5))
	var a9 []string = []string{"a", "b", "c", "d"}
	fmt.Printf("%v\n", len(a9))
	if 1 != 0 {
		fmt.Printf("%v\n", "World is sane")
	}
}

func main() {
	show()
}
