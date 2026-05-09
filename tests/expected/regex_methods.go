package main

import (
	"fmt"
	"regexp"
)

func TestReMethods() {
	var text string = "The quick brown fox jumps over the lazy dog"
	search_res := regexp.MustCompile("fox").FindStringIndex(text) != nil
	if search_res {
		fmt.Printf("%v\n", "Found fox")
	}
	match_res := regexp.MustCompile("^"+"The").FindStringIndex(text) != nil
	if match_res {
		fmt.Printf("%v\n", "Matched The")
	}
	var findall_res []string = regexp.MustCompile("\\w+").FindAllString(text, -1)
	fmt.Printf("%v\n", len(findall_res))
	sub_res := regexp.MustCompile("fox").ReplaceAllString(text, "cat")
	fmt.Printf("%v\n", sub_res)
	var split_res []string = regexp.MustCompile("\\s+").Split(text, -1)
	fmt.Printf("%v\n", len(split_res))
	pattern := regexp.MustCompile("\\d+")
	fmt.Printf("%v\n", "Pattern compiled")
}

func main() {
	TestReMethods()
}
