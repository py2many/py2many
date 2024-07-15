// generated by py2many --d=1
import std;
import std.algorithm : equal;

int bisect_right(int[] data, int item) {
  int low = 0;
  int high = data.length.to!int;
  while (low < high) {
    int middle = ((low + high) / 2).to!int;

    if (item < data[middle]) {
      high = middle;
    } else {
      low = (middle + 1);
    }
  }
  return low;
}

int[] bin_it(int[] limits, int[] data) {
  int[] bins = [0];
  foreach (_x; limits) {
    bins ~= (0);
  }
  foreach (d; data) {
    bins[bisect_right(limits, d)] += 1;
  }
  return bins;
}

void main(string[] argv) {
  int[] limits = [23, 37, 43, 53, 67, 83];
  int[] data = [
    95, 21, 94, 12, 99, 4, 70, 75, 83, 93, 52, 80, 57, 5, 53, 86, 65, 17, 92,
    83, 71, 61, 54, 58, 47, 16, 8, 9, 32, 84, 7, 87, 46, 19, 30, 37, 96, 6,
    98, 40, 79, 97, 45, 64, 60, 29, 49, 36, 43, 55
  ];
  assert(equal(bin_it(limits, data), [11, 4, 2, 6, 9, 5, 13]));
  writeln(format("%s", "OK"));
}
