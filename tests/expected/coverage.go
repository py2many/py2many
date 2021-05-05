package main

import (
	"fmt"
	"github.com/adsharma/py2many/pygo/runtime"
	iter "github.com/hgfischer/go-iter"
)

func do_pass() {
	/* pass */
}

func inline_pass() {
	/* pass */
}

func indexing() int {
	var sum int = 0
	var a []int = []int{}
	for _, i := range iter.NewIntSeq(iter.Start(0), iter.Stop(10)).All() {
		a = append(a, i)
		sum += a[i]
	}
	return sum
}

func infer_bool(code int) bool {
	return pygo.Contains([]int{1, 2, 4}, code)
}

func show() {
	var a1 int = 10
	var b9 int = 2
	var b2 int = 2
	if !(b2 == b9) {
		panic("assert")
	}
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
	a6 := map[int]bool{1: true, 2: true, 3: true, 4: true}
	fmt.Printf("%v\n", len(a6))
	a7 := map[string]int{"a": 1, "b": 2}
	fmt.Printf("%v\n", len(a7))
	var a8 bool = true
	if a8 {
		fmt.Printf("%v\n", "true")
	} else {
		if a4 > 0 {
			fmt.Printf("%v\n", "never get here")
		}
	}
	if a1 == 11 {
		fmt.Printf("%v\n", "false")
	} else {
		fmt.Printf("%v\n", "true")
	}
	if 1 != 0 {
		fmt.Printf("%v\n", "World is sane")
	}
	do_pass()
	inline_pass()
	var s string = "1    2"
	fmt.Printf("%v\n", s)
}

func main() {
	show()
}
