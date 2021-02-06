
fun bisect_right(data: Array<Int>, item: Int): Int {
var low = 0
var high = data_.len()
while (low < high) {
middle = i32::from(((low + high)/2))
if(item < data_[middle]) {
high = middle;
} else {
low = (middle + 1);
}
}
return low}


fun bin_it(limits: Array<Int>, data: Array<Int>): Array<Int> {
let var bins = vec![0];
for x in limits {
bins.push(0)
}
for d in data_ {
bins[bisect_right(limits, d)] += 1;
}
return bins}


