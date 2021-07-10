
proc test(): int =
  let a: seq[int] = @[1, 2, 3]
  return a[1]

proc main() =
  let b = test()
  assert(b == 2)
  echo "OK"

main()
