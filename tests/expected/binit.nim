
proc bisect_right(data: openArray<int>, item: int): int =
    mut low = 0
    mut high = len(data)
    while low < high:
        middle = i32::from(low + high / 2)
        if item < data[middle]:
            high = middle;
else:
            low = middle + 1;
    return low
proc bin_it(limits: openArray<int>, data: openArray<int>): openArray<int> =
    let mut bins = vec![0];
    for x in limits:
        bins.push(0)
    for d in data:
        bins[bisect_right(limits, d)] += 1;
    return bins
