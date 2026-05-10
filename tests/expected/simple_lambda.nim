proc show() =
  let f = proc(x: int): int = return (x + 1)
  echo f(5)

proc main() =
  show()

main()
