package main

import (
	"fmt"
	"strings"
)

func SumAll(nums ...int) int {
	var total int = 0
	for _, n := range nums {
		total += n
	}
	return total
}

func MainFunc() {
	fmt.Printf("%v\n", strings.Repeat("a", 5))
	fmt.Printf("%v\n", func() string {
		items := func() []int {
			var out []int
			for i := 0; i < 3; i++ {
				out = append(out, []int{0}...)
			}
			return out
		}()
		parts := make([]string, len(items))
		for i, item := range items {
			switch v := any(item).(type) {
			case string:
				parts[i] = fmt.Sprintf("'%s'", strings.ReplaceAll(v, "'", "\\'"))
			default:
				parts[i] = fmt.Sprintf("%v", item)
			}
		}
		return "[" + strings.Join(parts, ", ") + "]"
	}())
	var numbers []int = []int{1, 2, 3}
	fmt.Printf("%v\n", SumAll(numbers...))
	var others []int = []int{4, 5}
	var all_nums []int = append(append(append([]int{0}, numbers...), others...), []int{6}...)
	fmt.Printf("%v\n", func() string {
		items := all_nums
		parts := make([]string, len(items))
		for i, item := range items {
			switch v := any(item).(type) {
			case string:
				parts[i] = fmt.Sprintf("'%s'", strings.ReplaceAll(v, "'", "\\'"))
			default:
				parts[i] = fmt.Sprintf("%v", item)
			}
		}
		return "[" + strings.Join(parts, ", ") + "]"
	}())
	var data []int = []int{10, 20, 30, 40, 50}
	var a int = 0
	var rest []int = []int{}
	var e int = 0
	__tmp27_4 := data
	a = __tmp27_4[0]
	rest = __tmp27_4[1 : len(__tmp27_4)-1]
	e = __tmp27_4[len(__tmp27_4)-1]
	fmt.Printf("%v\n", a)
	fmt.Printf("%v\n", func() string {
		items := rest
		parts := make([]string, len(items))
		for i, item := range items {
			switch v := any(item).(type) {
			case string:
				parts[i] = fmt.Sprintf("'%s'", strings.ReplaceAll(v, "'", "\\'"))
			default:
				parts[i] = fmt.Sprintf("%v", item)
			}
		}
		return "[" + strings.Join(parts, ", ") + "]"
	}())
	fmt.Printf("%v\n", e)
}

func main() {
	MainFunc()
}
