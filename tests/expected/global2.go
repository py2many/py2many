package main

import (
	"fmt"
	"github.com/adsharma/py2many/pygo"
)

var code_0 int = 0
var code_1 int = 1
var code_a string = "a"
var code_b string = "b"
var l_b = map[string]bool{code_a: true}
var l_c = map[string]int{code_b: code_0}

func main() {
	if !(pygo.MapContains(l_b, "a")) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}
