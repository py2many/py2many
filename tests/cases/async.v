@[translated]
module main

fn async_gen(ch chan any) {
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
