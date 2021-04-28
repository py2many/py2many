
proc show() =
  let myfunc = proc(x: int, y: int): int = return (x + y)
  echo myfunc(1, 2)

proc main() =
  show()

main()
