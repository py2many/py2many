
proc bubble_sort(seq: var seq[int]): seq[int] =
  let L = len(seq)
  for _ in (0..L - 1):
    for n in (1..L - 1):
      if seq[n] < seq[(n - 1)]:
        if true:
          let (tmp1, tmp2) = (seq[n], seq[(n - 1)])
          seq[(n - 1)] = tmp1
          seq[n] = tmp2


  return seq

proc main() =
  var unsorted = @[14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
  let expected = @[5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
  assert(bubble_sort(unsorted) == expected)
  echo "OK"

main()
