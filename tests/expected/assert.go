package main

func compare_assert(a int, b int) {
	if !(a == b) {
		panic("assert")
	}
}
