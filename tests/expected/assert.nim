proc compare_assert(a: int, b: int) =
  assert(a == b)

proc main() =
  compare_assert(1, 1)

main()
