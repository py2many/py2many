@[translated]
module main

type AnyFn = fn (Any) Any

type Any = bool | int | i64 | f64 | string | []byte | voidptr
type List = []Any

fn async_gen() chan Any {
	ch := chan Any{cap: 100}
	spawn fn [ch] () {
		defer { ch.close() }
		for i in 0 .. 3 {
			ch <- i
		}
	}()
	return ch
}

fn show_async() {
	// WARNING: async for converted to sync for
	for val in async_gen() {
		println(val.str())
	}
}

fn show() {
	asyncio.run(show_async())
}

fn main() {
	show()
}
