proc compare_assert(a: int, b: int) =
  assert(a == b)
  assert(not (0 == 1))

proc main() =
  compare_assert(1, 1)
  echo "OK"

