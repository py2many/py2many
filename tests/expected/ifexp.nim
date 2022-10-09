proc show() =
  let a = 1
  let b = if a in @[2, 3]: 2 else: 3
  echo b

proc main() =
  show()

main()
