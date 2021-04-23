package main

func compare_assert(a int, b int) {
	if !(a == b) {
		panic("assert")
	}
	if !(!(0 == 1)) {
		panic("assert")
	}
}

func main() {
	compare_assert(1, 1)
}
