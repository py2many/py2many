package main

import (
	"fmt"
	"github.com/google/go-cmp/cmp"
)

func BisectRight(data []int, item int) int {
	var low int = 0
	var high int = int(len(data))
	for low < high {
		var middle int = int(((low + high) / 2))
		if item < data[middle] {
			high = middle
		} else {
			low = (middle + 1)
		}
	}
	return low
}

func BinIt(limits []int, data []int) []int {
	var bins []int = []int{0}
	for _, _x := range limits {
		_ = _x
		bins = append(bins, 0)
	}
	for _, d := range data {
		bins[BisectRight(limits, d)] += 1
	}
	return bins
}

func main() {
	var limits []int = []int{23, 37, 43, 53, 67, 83}
	var data []int = []int{95, 21, 94, 12, 99, 4, 70, 75, 83, 93, 52, 80, 57, 5, 53, 86, 65, 17, 92, 83, 71, 61, 54, 58, 47, 16, 8, 9, 32, 84, 7, 87, 46, 19, 30, 37, 96, 6, 98, 40, 79, 97, 45, 64, 60, 29, 49, 36, 43, 55}
	if !(cmp.Equal(BinIt(limits, data), []int{11, 4, 2, 6, 9, 5, 13})) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}
