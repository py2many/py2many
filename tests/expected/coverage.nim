
proc indexing(): int =
  var sum = 0
  var a: seq[int] = @[]
  for i in (0..10 - 1):
    a.add(i)
    sum += a[i];
  return sum

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
  let sum1 = indexing()
  echo sum1
  let a5 = @[1, 2, 3]
  echo len(a5)
  let a9: seq[string] = @["a", "b", "c", "d"]
  echo len(a9)
  if 1 != 0:
    echo "World is sane"


proc main() =
  show()

main()
