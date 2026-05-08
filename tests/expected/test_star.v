@[translated]
module main

import arrays

fn sum_all(nums ...int) int {
	mut total := 0
	for n in nums {
		total += n
	}
	return total
}

fn main_func() {
	println(('a'.repeat(5)).str())
	println(([0].repeat(3)).str())
	numbers := [int(1), 2, 3]
	println((sum_all(...numbers.map(int(it)))).str())
	others := [int(4), 5]
	all_nums := arrays.concat(arrays.concat(arrays.concat([int(0)], ...numbers.map(int(it))),
		...others.map(int(it))), ...[int(6)])
	println(all_nums.str())
	data := [int(10), 20, 30, 40, 50]
	mut a := 0
	mut rest := []int{}
	mut e := 0
	__unpack1 := data
	a = __unpack1[0]
	rest = __unpack1[1..__unpack1.len - 1]
	e = __unpack1.last()
	println(a.str())
	println(rest.str())
	println(e.str())
}

fn main() {
	main_func()
}
