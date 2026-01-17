@[translated]
module main

import arrays

fn sum_all[A](nums ...A) int {
	mut total := 0
	for n in nums {
		total += n
	}
	return total
}

fn main_func() {
	println(('a'.repeat(5)).str())
	println(([0].repeat(3)).str())
	numbers := [1, 2, 3]
	println((sum_all(...numbers)).str())
	others := [4, 5]
	all_nums := arrays.concat(arrays.concat(arrays.concat([0], ...numbers), ...others),
		6)
	println(all_nums.str())
	data := [10, 20, 30, 40, 50]
	__unpack1 := data
	mut a := __unpack1[0]
	mut rest := __unpack1[1..__unpack1.len - 1]
	mut e := __unpack1.last()
	println(a.str())
	println(rest.str())
	println(e.str())
}

fn main() {
	main_func()
}
