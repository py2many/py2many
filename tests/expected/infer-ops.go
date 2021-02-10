package todo_naming

func foo() {
	a := 10
	b := 20
	c1 := (a + b)
	c2 := (a - b)
	c3 := (a * b)
	c4 := (a / b)
	c5 := -(a)
	d := 2.0
	e1 := (a + d)
	e2 := (a - d)
	e3 := (a * d)
	e4 := (a / d)
	f := -3.0
	g := -(a)
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

func fadd(x int8, y float64) float64 {
	return (x + y)
}
