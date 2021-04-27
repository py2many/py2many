
type Colors = enum
  RED,
  GREEN,
  BLUE,


type
  Permissions = enum
    R = 1,
    W = 2,
    X = 16,
  PermissionsFlags = set[Permissions]

proc show() =
  let color_map = [(Colors::RED, "red"), (Colors::GREEN, "green"), (Colors::BLUE, "blue")].iter().cloned().collect::<HashMap<_,_>>()
  let a = Colors::GREEN
  if a == Colors::GREEN:
    echo "green"
  else:
    echo "Not green"
  let b = Permissions::R
  if b == Permissions::R:
    echo "R"
  else:
    echo "Not R"
  assert(len(color_map) != 0)

proc main() =
  show()

main()
