package main

import (
	"fmt"
)

func Show() {
	var my_list []int = []int{1, 2, 3, 4, 5}
	my_list = append(my_list[:2], my_list[2+1:]...)
	fmt.Printf("%v\n", len(my_list))
	my_dict := map[string]int{"a": 1, "b": 2, "c": 3}
	delete(my_dict, "b")
	fmt.Printf("%v\n", len(my_dict))
}

func main() {
	Show()
}
