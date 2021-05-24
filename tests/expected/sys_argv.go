package main

import (
	"fmt"
	"os"
	"strings"
)

func main() {
	var a []string = os.Args
	var cmd string = a[0]
	if !(strings.Contains(cmd, "sys_argv")) {
		panic("assert")
	}
	if len(a) > 1 {
		fmt.Printf("%v\n", a[1])
	} else {
		fmt.Printf("%v\n", "OK")
	}
}
