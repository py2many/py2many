import sets
import tables

proc do_pass() =
  discard

proc inline_pass() =
  discard

proc indexing(): int =
  var sum = 0
  var a: seq[int] = @[]
  for i in (0..10 - 1):
    a.add(i)
    sum += a[i];
  return sum

proc infer_bool(code: int): bool =
  return code in @[1, 2, 4]

proc show() =
  let a1 = 10
  let b1 = 15
  let b2 = 15
  assert(b1 == 15)
  assert(b2 == 15)
  let b9 = 2
  let b10 = 2
  assert(b9 == b10)
  let a2: float64 = 2.1
  echo a2
  for i in (0..10 - 1):
    echo i
  for i in countup(0, 10 - 1, 2):
    echo i
  let a3 = -(a1)
  let a4 = (a3 + a1)
  echo a4
  let sum1 = indexing()
  echo sum1
  let a5 = @[1, 2, 3]
  echo len(a5)
  let a9: seq[string] = @["a", "b", "c", "d"]
  echo len(a9)
  let a6 = toHashSet([1, 2, 3, 4])
  echo len(a6)
  let a7 = {"a": 1, "b": 2}.newTable
  echo len(a7)
  let a8 = true
  if a8:
    echo "true"
  else:
    if a4 > 0:
      echo "never get here"

  if a1 == 11:
    echo "false"
  else:
    echo "true"
  if 1 != 0:
    echo "World is sane"

  do_pass()
  inline_pass()
  let s = "1    2"
  echo s

proc main() =
  show()

main()
