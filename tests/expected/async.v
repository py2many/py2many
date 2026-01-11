@[translated]
module main

type Any = bool | int | i64 | f64 | string | []byte

fn async_gen(ch chan Any) {
	defer { ch.close() }
	for i in 0 .. 3 {
		ch <- i
	}
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
