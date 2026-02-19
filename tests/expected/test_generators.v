[translated]
module main

type Any = bool | int | i64 | f64 | string | []byte

// Test cases for generator functions and yield statements

fn simple_generator(ch chan int) {
	defer { ch.close() }
	ch <- 1
	ch <- 2
	ch <- 3
}

fn generator_with_type(ch chan int) {
	defer { ch.close() }
	mut x := 0
	for x < 5 {
		ch <- x
		x += 1
	}
}

fn generator_with_args(a int, b int, ch chan Any) {
	defer { ch.close() }
	for i in a .. b {
		ch <- (int(i) * 2)
	}
}

fn inner(ch chan int) {
	defer { ch.close() }
	ch <- 1
	ch <- 2
}

fn generator_with_yield_from(ch chan int) {
	defer { ch.close() }
	__gen2 := (fn () chan int {
		__ch1 := chan int{}
		spawn inner(__ch1)
		return __ch1
	}())
	// yield from __gen2
	for {
		val := <-__gen2 or { break }
		ch <- val
	}
	ch <- 3
}

fn generator_with_condition(ch chan Any) {
	defer { ch.close() }
	for i in 0 .. 10 {
		if (int(i) % 2) == 0 {
			ch <- i
		}
	}
}

fn test_generator_calls() {
	gen1 := (fn () chan int {
		__ch3 := chan int{}
		spawn simple_generator(__ch3)
		return __ch3
	}())
	gen2 := (fn () chan Any {
		__ch4 := chan Any{}
		spawn generator_with_args(1, 5, __ch4)
		return __ch4
	}())
}
