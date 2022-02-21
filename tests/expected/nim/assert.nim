proc compare_assert(a: int, b: int) =
  assert(a == b)
  assert(not (0 == 1))

proc main() =
  assert(true)
  assert(not (false))
  compare_assert(1, 1)
  assert(true)
  assert(true)
  echo "OK"

main()
