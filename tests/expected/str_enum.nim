import tables

type Colors = enum
  RED = "red",
  GREEN = "green",
  BLUE = "blue",


proc show() =
  let color_map = {Colors.RED: "1", Colors.GREEN: "2",
      Colors.BLUE: "3"}.newTable
  let a = Colors.GREEN
  if a == Colors.GREEN:
    echo "green"
  else:
    echo "Not green"
  echo len(color_map)

proc main() =
  show()

main()
