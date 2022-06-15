from math import floor

proc comb_sort(seq: var seq[int]): seq[int] =
  var gap = len(seq)
  var swap = true
  while gap > 1 or swap:
    gap = max(1, int(floor((float64(gap) / 1.25))))
    swap = false
    for i in (0..(len(seq) - gap) - 1):
      if seq[i] > seq[(i + gap)]:
        if true:
          let (tmp1, tmp2) = (seq[(i + gap)], seq[i])
          seq[i] = tmp1
          seq[(i + gap)] = tmp2

        swap = true

  return seq

proc main() =
  var unsorted = @[14, 11, 19, 5, 16, 10, 19, 12, 5, 12]
  let expected = @[5, 5, 10, 11, 12, 12, 14, 16, 19, 19]
  assert(comb_sort(unsorted) == expected)
  echo "OK"

main()
