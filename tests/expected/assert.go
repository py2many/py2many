package main

func compare_assert(a int, b int) {
	if !(a == b) {
		panic("assert")
	}
}

func main() {
	compare_assert(1, 1)
}
