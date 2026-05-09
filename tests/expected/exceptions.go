package main

import (
	"fmt"
	"strings"
)

func Show() {
	{
		// try unsupported

		e := fmt.Errorf("foo")
		fmt.Printf("%v\n", "caught")
		// finally unsupported

		fmt.Printf("%v\n", "Finally")
	}
	{
		// try unsupported

		fmt.Printf("%v\n", "Got it")
	}
	{
		// try unsupported

		e := fmt.Errorf("foo")
		if !(strings.Contains(fmt.Sprintf("%v", e), "foo")) {
			panic("assert")
		}
	}
}

func main() {
	Show()
}
