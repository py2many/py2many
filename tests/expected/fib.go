package todo_naming

func fib(i int) int {
	if i == 0 || i == 1 {
		return 1
	}
	return (fib((i - 1)) + fib((i - 2)))
}
