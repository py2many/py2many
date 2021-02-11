package todo_naming

type Rectangle struct {
	height int
	length int
}

func is_square(self Rectangle) bool {
	return self.height == self.length
}
