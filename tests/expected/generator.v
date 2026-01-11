@[translated]
module main

fn simple_generator(ch chan int) {
	defer { ch.close() }
	ch <- 1
	ch <- 2
	ch <- 3
}

fn show() {
	gen := (fn () chan int {
		__ch1 := chan int{}
		spawn simple_generator(__ch1)
		return __ch1
	}())
	for {
		val := <-gen or { break }
		println(val.str())
	}
}

fn main() {
	show()
}
