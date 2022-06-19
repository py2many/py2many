package main

import (
	"fmt"
	"github.com/electrious/refutil"
)

func NestedContainers() bool {
	CODES := map[string][]int{"KEY": []int{1, 3}}
	return refutil.Contains(CODES["KEY"], 1)
}

func main() {
	if NestedContainers() {
		fmt.Printf("%v\n", "OK")
	}
}
