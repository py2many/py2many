package main

import (
	"fmt"
)

func DoUnsupported() {
	var a int = 1
	// dict comprehension ((key + 1), (value + 1)) unimplemented on line 9:4;
	var b bool = (a != 0)
	if b {
		fmt.Printf("%v\n", "True")
	} else {
		fmt.Printf("%v\n", "False")
	}
}

func main() {
	DoUnsupported()
}
