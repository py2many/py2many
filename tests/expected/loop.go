package main

import (
	"fmt"
	iter "github.com/hgfischer/go-iter"
)

func ForWithBreak() {
	for _, i := range iter.NewIntSeq(iter.Start(0), iter.Stop(4)).All() {
		if i == 2 {
			break
		}
		fmt.Printf("%v\n", i)
	}
}

func ForWithContinue() {
	for _, i := range iter.NewIntSeq(iter.Start(0), iter.Stop(4)).All() {
		if i == 2 {
			continue
		}
		fmt.Printf("%v\n", i)
	}
}

func ForWithElse() {
	var has_break bool = false
	for _, i := range iter.NewIntSeq(iter.Start(0), iter.Stop(4)).All() {
		fmt.Printf("%v\n", i)
	}
	if has_break != true {
		fmt.Printf("%v\n", "OK")
	}
}

func WhileWithBreak() {
	var i int = 0
	for true {
		if i == 2 {
			break
		}
		fmt.Printf("%v\n", i)
		i += 1
	}
}

func WhileWithContinue() {
	var i int = 0
	for i < 5 {
		i += 1
		if i == 2 {
			continue
		}
		fmt.Printf("%v\n", i)
	}
}

func main() {
	ForWithBreak()
	ForWithContinue()
	ForWithElse()
	WhileWithBreak()
	WhileWithContinue()
}
