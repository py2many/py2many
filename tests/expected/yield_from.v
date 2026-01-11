@[translated]
module main

fn generator1(ch chan int) {
	defer { ch.close() }
	ch <- 1
	ch <- 2
	ch <- 3
}

fn generator2(ch chan int) {
	defer { ch.close() }
	ch <- 0
	__gen2 := (fn () chan int {
		__ch1 := chan int{}
		spawn generator1(__ch1)
		return __ch1
	}())
	// yield from __gen2
	for {
		val := <-__gen2 or { break }
		ch <- val
	}
	ch <- 4
}

fn show() {
	gen := (fn () chan int {
		__ch3 := chan int{}
		spawn generator2(__ch3)
		return __ch3
	}())
	for {
		val := <-gen or { break }
		println(val.str())
	}
}

fn main() {
	show()
}
