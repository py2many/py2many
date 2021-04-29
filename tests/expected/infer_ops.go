package main

import (
	"fmt"
)

func foo() {
	var a int = 10
	var b int = 20
	var c1 int = (a + b)
	var c2 int = (a - b)
	var c3 int = (a * b)
	var c4 float64 = float64((a / b))
	var c5 int = -(a)
	var d float64 = 2.0
	var e1 float64 = (a + d)
	var e2 float64 = (a - d)
	var e3 float64 = (a * d)
	var e4 float64 = (a / d)
	var f float64 = -3.0
	var g int = -(a)
}

func add1(x int8, y int8) int16 {
	return (x + y)
}

func add2(x int16, y int16) int32 {
	return (x + y)
}

func add3(x int32, y int32) int64 {
	return (x + y)
}

func add4(x int64, y int64) int64 {
	return (x + y)
}

func add5(x uint8, y uint8) uint16 {
	return (x + y)
}

func add6(x uint16, y uint16) uint32 {
	return (x + y)
}

func add7(x uint32, y uint32) uint64 {
	return (x + y)
}

func add8(x uint64, y uint64) uint64 {
	return (x + y)
}

func add9(x int8, y uint16) uint32 {
	return (x + y)
}

func sub(x int8, y int8) int8 {
	return (x - y)
}

func mul(x int8, y int8) int16 {
	return (x * y)
}

func fadd1(x int8, y float64) float64 {
	return (x + y)
}

func show() {
	var rv float64 = fadd1(6, 6.0)
	if !(rv == 12) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}

func main() {
	foo()
	show()
}
