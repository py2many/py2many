package main

import (
	"fmt"
	iter "github.com/hgfischer/go-iter"
)

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
}

func main() {
	show()
}
