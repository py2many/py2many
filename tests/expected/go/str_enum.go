package main

import (
	"fmt"
)

type Colors string

const (
	RED   Colors = "red"
	GREEN        = "green"
	BLUE         = "blue"
)

func Show() {
	color_map := map[Colors]string{RED: "1", GREEN: "2", BLUE: "3"}
	var a Colors = GREEN
	if a == GREEN {
		fmt.Printf("%v\n", "green")
	} else {
		fmt.Printf("%v\n", "Not green")
	}
	fmt.Printf("%v\n", len(color_map))
}

func main() {
	Show()
}
