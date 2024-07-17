// @dart=3.4
import 'package:collection/collection.dart';
import 'package:sprintf/sprintf.dart';

int bisect_right(List<int> data, int item) {
  int low = 0;
  int high = data.length.toInt();
  while (low < high) {
    final int middle = ((low + high) ~/ 2).toInt();

    if (item < (data[middle] ?? (throw Exception("key not found")))) {
      high = middle;
    } else {
      low = (middle + 1);
    }
  }
  return low;
}

List<int> bin_it(List<int> limits, List<int> data) {
  List<int> bins = [0];
  for (final _x in limits) {
    bins.add(0);
  }
  for (final d in data) {
    bins[bisect_right(limits, d)] += 1;
  }
  return bins;
}

main(List<String> argv) {
  final List<int> limits = [23, 37, 43, 53, 67, 83];
  final List<int> data = [
    95,
    21,
    94,
    12,
    99,
    4,
    70,
    75,
    83,
    93,
    52,
    80,
    57,
    5,
    53,
    86,
    65,
    17,
    92,
    83,
    71,
    61,
    54,
    58,
    47,
    16,
    8,
    9,
    32,
    84,
    7,
    87,
    46,
    19,
    30,
    37,
    96,
    6,
    98,
    40,
    79,
    97,
    45,
    64,
    60,
    29,
    49,
    36,
    43,
    55
  ];
  assert(DeepCollectionEquality()
      .equals(bin_it(limits, data), [11, 4, 2, 6, 9, 5, 13]));
  print(sprintf("%s", ["OK"]));
}
