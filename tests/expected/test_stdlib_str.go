package main

import (
	"fmt"
	"regexp"
	"strings"
	"unicode"
)

func TestStrMethods() {
	var s string = "  Hello World  "
	fmt.Printf("%v\n", strings.ToLower(s))
	fmt.Printf("%v\n", strings.ToUpper(s))
	fmt.Printf("%v\n", (strings.ToUpper(s[:1]) + strings.ToLower(s[1:])))
	fmt.Printf("%v\n", strings.TrimSpace(s))
	fmt.Printf("%v\n", strings.TrimLeftFunc(s, unicode.IsSpace))
	fmt.Printf("%v\n", strings.TrimRightFunc(s, unicode.IsSpace))
	var parts []string = strings.Fields(s)
	fmt.Printf("%v\n", func() string {
		items := parts
		parts := make([]string, len(items))
		for i, item := range items {
			switch v := any(item).(type) {
			case string:
				parts[i] = fmt.Sprintf("%q", v)
			default:
				parts[i] = fmt.Sprintf("%v", item)
			}
		}
		return "[" + strings.Join(parts, ", ") + "]"
	}())
	joined := strings.Join([]string{"a", "b", "c"}, "-")
	fmt.Printf("%v\n", joined)
	fmt.Printf("%v\n", strings.Index(s, "World"))
	fmt.Printf("%v\n", strings.ReplaceAll(s, "World", "Vlang"))
	if regexp.MustCompile(`^\d+$`).MatchString("123") {
		fmt.Printf("%v\n", "digit")
	}
	if regexp.MustCompile(`^[A-Za-z]+$`).MatchString("abc") {
		fmt.Printf("%v\n", "alpha")
	}
	if regexp.MustCompile(`^\s+$`).MatchString("   ") {
		fmt.Printf("%v\n", "space")
	}
}

func main() {
	TestStrMethods()
}
