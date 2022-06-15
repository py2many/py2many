proc foo() =
  let a = 10
  let b = a
  assert(b == 10)
  echo b

proc main() =
  foo()

main()
