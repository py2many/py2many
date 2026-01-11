@[translated]
module main

type Any = bool | int | i64 | f64 | string | []byte

fn show() {
	squares := (fn () map[int]Any {
		mut result := map[int]Any{}
		for x in 0 .. 5 {
			result[x] = (x * x)
		}
		return result
	}())
	println((squares.len).str())
	evens := (fn () map[int]Any {
		mut result := map[int]Any{}
		for x in 0 .. 10 {
			if (int(x) % 2) == 0 {
				result[x] = (int(x) * 2)
			}
		}
		return result
	}())
	println((evens.len).str())
}

fn main() {
	show()
}
