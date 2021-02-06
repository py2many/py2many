
int bisect_right(Array<int> data, int item) {
int low = 0;
var high = data.len();
while (low < high) {
var middle = i32::from(((low + high)/2));


if(item < data[middle]) {
high = middle;
} else {
low = (middle + 1);
}
}
return low;}


Array<int> bin_it(Array<int> limits, Array<int> data) {
var bins = [0];
for x in limits {
bins.push(0);
}
for d in data {
bins[bisect_right(limits, d)] += 1;
}
return bins;}


