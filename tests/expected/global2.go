package main

import (
	"fmt"
	"github.com/electrious/refutil"
)

var Code0 int = 0
var Code1 int = 1
var CodeA string = "a"
var CodeB string = "b"
var LB = map[string]bool{CodeA: true}
var LC = map[string]int{CodeB: Code0}

func main() {
	if !(refutil.ContainsKey(LB, "a")) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}
