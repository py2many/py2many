package main

import (
	"fmt"
	"github.com/adsharma/py2many/pygo/runtime"
)

func NestedContainers() bool {
	CODES := map[string][]int{"KEY": []int{1, 3}}
	return pygo.Contains(CODES["KEY"], 1)
}

func main() {
	if NestedContainers() {
		fmt.Printf("%v\n", "OK")
	}
}
