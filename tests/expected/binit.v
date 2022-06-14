[translated]
module main

fn bisect_right(data []int, item int) int {
	mut low := 0
	mut high := int(data.len)
	for low < high {
		middle := int(((low + high) / 2))
		if item < data[middle] {
			high = middle
		} else {
			low = (middle + 1)
		}
	}
	return low
}

fn bin_it(limits []int, data []int) []int {
	mut bins := [0]
	for _x in limits {
		bins << (0)
	}
	for d in data {
		bins[bisect_right(limits, d)] += 1
	}
	return bins
}

fn main() {
	limits := [23, 37, 43, 53, 67, 83]
	data := [95, 21, 94, 12, 99, 4, 70, 75, 83, 93, 52, 80, 57, 5, 53, 86, 65, 17, 92, 83, 71,
		61, 54, 58, 47, 16, 8, 9, 32, 84, 7, 87, 46, 19, 30, 37, 96, 6, 98, 40, 79, 97, 45, 64,
		60, 29, 49, 36, 43, 55]
	assert bin_it(limits, data) == [11, 4, 2, 6, 9, 5, 13]
	println('OK')
}
