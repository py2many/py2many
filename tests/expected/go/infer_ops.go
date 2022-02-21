package main

import (
	"fmt"
)

func Foo() {
	var a int = 10
	var b int = 20
	var _c1 int = (a + b)
	_ = _c1
	var _c2 int = (a - b)
	_ = _c2
	var _c3 int = (a * b)
	_ = _c3
	var _c4 float64 = float64((a / b))
	_ = _c4
	var _c5 int = -(a)
	_ = _c5
	var d float64 = 2.0
	var _e1 float64 = (float64(a) + d)
	_ = _e1
	var _e2 float64 = (float64(a) - d)
	_ = _e2
	var _e3 float64 = (float64(a) * d)
	_ = _e3
	var _e4 float64 = (float64(a) / d)
	_ = _e4
	var _f float64 = -3.0
	_ = _f
	var _g int = -(a)
	_ = _g
}

func Add1(x int8, y int8) int16 {
	return int16((x + y))
}

func Add2(x int16, y int16) int32 {
	return int32((x + y))
}

func Add3(x int32, y int32) int64 {
	return int64((x + y))
}

func Add4(x int64, y int64) int64 {
	return (x + y)
}

func Add5(x uint8, y uint8) uint16 {
	return uint16((x + y))
}

func Add6(x uint16, y uint16) uint32 {
	return uint32((x + y))
}

func Add7(x uint32, y uint32) uint64 {
	return uint64((x + y))
}

func Add8(x uint64, y uint64) uint64 {
	return (x + y)
}

func Add9(x int8, y uint16) uint32 {
	return uint32((uint16(x) + y))
}

func Sub(x int8, y int8) int8 {
	return (x - y)
}

func Mul(x int8, y int8) int16 {
	return int16((x * y))
}

func Fadd1(x int8, y float64) float64 {
	return (float64(x) + y)
}

func Show() {
	if !(Fadd1(6, 6.0) == 12) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}

func main() {
	Foo()
	Show()
}
