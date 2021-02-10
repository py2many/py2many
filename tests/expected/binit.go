package todo_naming

func bisect_right(data []int, item int) int {
	low := 0
	high := len(data)
	for low < high {
		middle := int(((low + high) / 2))
		if item < data[middle] {
			high := middle
		} else {
			low := (middle + 1)
		}
	}
	return low
}

func bin_it(limits []int, data []int) []int {
	bins := [...]int{0}
	for limits := range x {
		bins.push(0)
	}
	for data := range d {
		bins[bisect_right(limits, d)] += 1
	}
	return bins
}
