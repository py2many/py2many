package main

import (
	"fmt"
	"github.com/google/go-cmp/cmp"
	iter "github.com/hgfischer/go-iter"
	"math"
)

func CombSort(seq []int) []int {
	gap := len(seq)
	var swap bool = true
	for gap > 1 || swap {
		gap = int(math.Max(1, math.Floor((float64(gap) / 1.25))))
		swap = false
		for _, i := range iter.NewIntSeq(iter.Start(0), iter.Stop((len(seq) - gap))).All() {
			if seq[i] > seq[(i+gap)] {
				{
					var __tmp1, __tmp2 = seq[(i + gap)], seq[i]
					seq[i] = __tmp1
					seq[(i + gap)] = __tmp2
				}
				swap = true
			}
		}
	}
	return seq
}

func main() {
	var unsorted []int = []int{14, 11, 19, 5, 16, 10, 19, 12, 5, 12}
	var expected []int = []int{5, 5, 10, 11, 12, 12, 14, 16, 19, 19}
	if !(cmp.Equal(CombSort(unsorted), expected)) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}
