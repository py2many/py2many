package main

import (
	"fmt"
)

func Show() {
	{
		// try unsupported

		fmt.Printf("%v\n", "ZeroDivisionError")
	}
}

func main() {
	Show()
}
