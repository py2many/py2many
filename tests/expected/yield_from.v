@[translated]
module main

fn generator1() chan int {
	ch := chan int{cap: 100}
	spawn fn [ch] () {
		defer { ch.close() }
		ch <- 1
		ch <- 2
		ch <- 3
	}()
	return ch
}

fn generator2() chan int {
	ch := chan int{cap: 100}
	spawn fn [ch] () {
		defer { ch.close() }
		ch <- 0
		__gen1 := generator1()
		// yield from __gen1
		for {
			val := <-__gen1 or { break }
			ch <- val
		}
		ch <- 4
	}()
	return ch
}

fn show() {
	gen := generator2()
	for {
		val := <-gen or { break }
		println(val.str())
	}
}

fn main() {
	show()
}
