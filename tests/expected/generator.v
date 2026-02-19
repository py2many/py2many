@[translated]
module main

fn simple_generator() chan int {
	ch := chan int{cap: 100}
	spawn fn [ch] () {
		defer { ch.close() }
		ch <- 1
		ch <- 2
		ch <- 3
	}()
	return ch
}

fn show() {
	gen := simple_generator()
	for {
		val := <-gen or { break }
		println(val.str())
	}
}

fn main() {
	show()
}
