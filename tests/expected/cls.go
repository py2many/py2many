package main

import (
	"fmt"
)

type Foo struct {
}

func bar(self Foo) string {
	return "a"
}

func main() {
	var f Foo = Foo{}
	b := bar(f)
	fmt.Printf("%v\n", b)
}
