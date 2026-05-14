@[translated]
module main

fn bubble_sort(mut seq []int) []int {
	l := seq.len
	for _ in 0 .. l {
		for n in 1 .. l {
			if seq[n] < seq[((n as int) - 1)] {
				__unpack1, __unpack2 := [seq[n], seq[((n as int) - 1)]]
				seq[((n as int) - 1)] = __unpack1
				seq[n] = __unpack2
			}
		}
	}
	return seq
}

fn main() {
	mut unsorted := [14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
	expected := [5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
	assert bubble_sort(mut unsorted) == expected
	println('OK')
}
