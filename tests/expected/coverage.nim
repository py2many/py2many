proc show() =
  let a1 = 10
  let a2: float = 2.1
  echo a2
  for i in (0..10 - 1):
    echo i
  for i in countup(0, 10 - 1, 2):
    echo i
  let a3 = -(a1)
  let a4 = a3 + a1
  echo a4

proc main() =
  show()

main()
