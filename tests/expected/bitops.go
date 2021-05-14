package main

import (
	"fmt"
	"github.com/google/go-cmp/cmp"
)

func MainFunc() {
	var ands []bool = []bool{}
	var ors []bool = []bool{}
	var xors []bool = []bool{}
	for _, a := range []bool{false, true} {
		for _, b := range []bool{false, true} {
			ands = append(ands, (a && b))
			ors = append(ors, (a || b))
			xors = append(xors, (a != b))
		}
	}
	if !(cmp.Equal(ands, []bool{false, false, false, true})) {
		panic("assert")
	}
	if !(cmp.Equal(ors, []bool{false, true, true, true})) {
		panic("assert")
	}
	if !(cmp.Equal(xors, []bool{false, true, true, false})) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}

func main() {
	MainFunc()
}
