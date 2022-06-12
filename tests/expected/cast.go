package main

import (
	"fmt"
)

func MainFunc() {
	var a int16 = int16(1)
	b := a
	fmt.Printf("%v\n", b)
	var c int64 = int64(1)
	d := c
	fmt.Printf("%v\n", d)
	var e uint64 = uint64(1)
	f := e
	fmt.Printf("%v\n", f)
}

func main() {
	MainFunc()
}
