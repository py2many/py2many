package todo_naming

type Colors int

const (
	RED   Colors = iota
	GREEN        = iota
	BLUE         = iota
)

type Permissions int

const (
	R Permissions = 1
	W             = 2
	X             = 16
)
