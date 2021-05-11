package main

import (
	"fmt"
	"github.com/google/go-cmp/cmp"
	iter "github.com/hgfischer/go-iter"
)

func BubbleSort(seq []int) []int {
	L := len(seq)
	for range iter.NewIntSeq(iter.Start(0), iter.Stop(L)).All() {
		for _, n := range iter.NewIntSeq(iter.Start(1), iter.Stop(L)).All() {
			if seq[n] < seq[(n-1)] {
				{
					var __tmp1, __tmp2 = seq[n], seq[(n - 1)]
					seq[(n - 1)] = __tmp1
					seq[n] = __tmp2
				}
			}
		}
	}
	return seq
}

func main() {
	var unsorted []int = []int{14, 11, 19, 5, 16, 10, 19, 12, 5, 12}
	var expected []int = []int{5, 5, 10, 11, 12, 12, 14, 16, 19, 19}
	if !(cmp.Equal(BubbleSort(unsorted), expected)) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}
