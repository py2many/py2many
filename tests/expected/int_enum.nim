import tables

type Colors = enum
  RED,
  GREEN,
  BLUE,


type
  Permissions = enum
    R = 1,
    W = 2,
    X = 16,

proc show() =
  let color_map = {Colors.RED: "red", Colors.GREEN: "green",
      Colors.BLUE: "blue"}.newTable
  let a = Colors.GREEN
  if a == Colors.GREEN:
    echo "green"
  else:
    echo "Not green"
  let b = Permissions.R
  if b == Permissions.R:
    echo "R"
  else:
    echo "Not R"
  assert(len(color_map) != 0)

proc main() =
  show()

main()
