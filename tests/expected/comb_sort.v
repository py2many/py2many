@[translated]
module main

import arrays
import math

fn comb_sort(mut seq []int) []int {
	mut gap := seq.len
	mut swap := true
	for gap > 1 || swap {
		gap = arrays.max([1, int(math.floor((f64(gap) / 1.25)))]) or { panic('!') }
		swap = false
		for i in 0 .. (seq.len - gap) {
			if seq[i] > seq[(i + int(gap))] {
				__unpack1, __unpack2 := seq[(i + int(gap))], seq[i]
				seq[i] = __unpack1
				seq[(i + int(gap))] = __unpack2
				swap = true
			}
		}
	}
	return seq
}

fn main() {
	mut unsorted := [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
	expected := [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
	assert comb_sort(mut unsorted) == expected
	println('OK')
}
