
proc bisect_right(data: openArray[int], item: int): int =
  var low = 0
  var high = len(data)
  while low < high:
    let middle = int(low + high / 2)
    if item < data[middle]:
      high = middle;
    else:
      low = middle + 1;
  return low

proc bin_it(limits: openArray[int], data: openArray[int]): openArray[int] =
  bins = @[0]
  for x in limits:
    bins.push(0)
  for d in data:
    bins[bisect_right(limits, d)] += 1;
  return bins

