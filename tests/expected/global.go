package main

import (
	"fmt"
	"github.com/adsharma/py2many/pygo"
)

var code_0 int = 0
var code_1 int = 1
var l_a []int = []int{code_0, code_1}
var code_a string = "a"
var code_b string = "b"
var l_b []string = []string{code_a, code_b}

func main() {
	for _, i := range l_a {
		fmt.Printf("%v\n", i)
	}
	for _, i := range l_b {
		fmt.Printf("%v\n", i)
	}
	if pygo.Contains([]string{"a", "b"}, "a") {
		fmt.Printf("%v\n", "OK")
	}
}
