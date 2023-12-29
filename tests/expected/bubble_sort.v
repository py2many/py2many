@[translated]
module main

fn bubble_sort(mut seq []int) []int {
	L := seq.len
	for _ in 0 .. L {
		for n in 1 .. L {
			if seq[n] < seq[(int(n) - 1)] {
				seq[(int(n) - 1)], seq[n] = seq[n], seq[(int(n) - 1)]
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
