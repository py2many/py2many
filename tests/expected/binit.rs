use std::collections;

fn bisect_right(data: Vec<i32>, item: i32) -> i32 {
    let mut low: i32 = 0;
    let mut high: _ = data.len();
    while (low < high) {
        let middle: _ = i32::from(((low + high) / 2));
        if item < data[middle] {
            high = middle;
        } else {
            low = (middle + 1);
        }
    }
    return low;
}

fn bin_it(limits: Vec<i32>, data: Vec<i32>) -> Vec<i32> {
    let mut bins = vec![0];
    for x in limits {
        bins.push(0);
    }
    for d in data {
        bins[bisect_right(limits, d)] += 1;
    }
    return bins;
}
