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

fn generator_with_type() chan int {
	ch := chan int{cap: 100}
	spawn fn [ch] () {
		defer { ch.close() }
		mut x := 0
		for x < 5 {
			ch <- x
			x += 1
		}
	}()
	return ch
}

fn generator_with_args(a int, b int) chan int {
	ch := chan int{cap: 100}
	spawn fn [ch, a, b] () {
		defer { ch.close() }
		for i in a .. b {
			ch <- (i * 2)
		}
	}()
	return ch
}

fn inner() chan int {
	ch := chan int{cap: 100}
	spawn fn [ch] () {
		defer { ch.close() }
		ch <- 1
		ch <- 2
	}()
	return ch
}

fn generator_with_yield_from() chan int {
	ch := chan int{cap: 100}
	spawn fn [ch] () {
		defer { ch.close() }
		__gen1 := inner()
		// yield from __gen1
		for {
			val := <-__gen1 or { break }
			ch <- val
		}
		ch <- 3
	}()
	return ch
}

fn generator_with_condition() chan int {
	ch := chan int{cap: 100}
	spawn fn [ch] () {
		defer { ch.close() }
		for i in 0 .. 10 {
			if (i % 2) == 0 {
				ch <- i
			}
		}
	}()
	return ch
}

fn generator_calls() {
	gen1 := simple_generator()
	gen2 := generator_with_args(1, 5)
}

fn consume_generators() {
	__gen2 := simple_generator()
	for {
		val := <-__gen2 or { break }
		println(val.str())
	}
	__gen3 := generator_with_type()
	for {
		val := <-__gen3 or { break }
		println(val.str())
	}
	__gen4 := generator_with_args(1, 5)
	for {
		val := <-__gen4 or { break }
		println(val.str())
	}
	__gen5 := generator_with_yield_from()
	for {
		val := <-__gen5 or { break }
		println(val.str())
	}
	__gen6 := generator_with_condition()
	for {
		val := <-__gen6 or { break }
		println(val.str())
	}
}

fn main() {
	generator_calls()
	consume_generators()
}
