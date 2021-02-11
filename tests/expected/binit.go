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
	bins := []int{0}
	for x := range limits {
		bins = append(bins, 0)
	}
	for d := range data {
		bins[bisect_right(limits, d)] += 1
	}
	return bins
}
