package main

import (
	"fmt"
	"github.com/electrious/refutil"
	iter "github.com/hgfischer/go-iter"
	"strings"
)

func InlinePass() {
	// pass
}

func InlineEllipsis() {
	// ...
}

func Indexing() int {
	var sum int = 0
	var a []int = []int{}
	for _, i := range iter.NewIntSeq(iter.Start(0), iter.Stop(10)).All() {
		a = append(a, i)
		sum += a[i]
	}
	return sum
}

func InferBool(code int) bool {
	return refutil.Contains([]int{1, 2, 4}, code)
}

func Show() {
	var a1 int = 10
	var b1 int = 15
	var b2 int = 15
	if !(b1 == 15) {
		panic("assert")
	}
	if !(b2 == 15) {
		panic("assert")
	}
	var b9 int = 2
	var b10 int = 2
	if !(b9 == b10) {
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
	var t1 int
	if a1 > 5 {
		t1 = 10
	} else {
		t1 = 5
	}
	if !(t1 == 10) {
		panic("assert")
	}
	var sum1 int = Indexing()
	fmt.Printf("%v\n", sum1)
	var a5 []int = []int{1, 2, 3}
	fmt.Printf("%v\n", len(a5))
	var a9 []string = []string{"a", "b", "c", "d"}
	fmt.Printf("%v\n", len(a9))
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
	if true {
		fmt.Printf("%v\n", "True")
	} else {
		fmt.Printf("%v\n", "False")
	}
	if true {
		a1 += 1
	}
	if !(a1 == 11) {
		panic("assert")
	}
	if true {
		fmt.Printf("%v\n", "true")
	}
	InlinePass()
	var s string = "1    2"
	fmt.Printf("%v\n", s)
	if !(InferBool(1)) {
		panic("assert")
	}
	var _escape_quotes string = " foo \"bar\" baz "
	_ = _escape_quotes
	if !(strings.Contains("aaabbccc", "bbc")) {
		panic("assert")
	}
	if !(1 != 0) {
		panic("assert")
	}
	var _c1 int = 1
	_ = _c1
	_ = 2
	var _c2 int = 3
	_ = _c2
}

func main() {
	Show()
}
