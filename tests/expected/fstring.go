package main

import (
	"fmt"
	"strings"
)

func main() {
	var a int = 10
	fmt.Printf("%v\n", strings.Join([]string{"hello ", fmt.Sprintf("%v", (a + 1)), " world"}, ""))
}
