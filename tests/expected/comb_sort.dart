// @dart=3.4
import 'dart:math';
import 'package:collection/collection.dart';
import 'package:sprintf/sprintf.dart';
import 'package:tuple/tuple.dart';

List<int> comb_sort(List<int> seq) {
  var gap = seq.length;
  bool swap = true;
  while (gap > 1 || swap) {
    gap = max(1, (gap / 1.25).floor());
    swap = false;
    for (final i in ([for (var i = 0; i < (seq.length - gap); i += 1) i])) {
      if ((seq[i] ?? (throw Exception("key not found"))) >
          (seq[(i + gap)] ?? (throw Exception("key not found")))) {
        final __tmp1 = Tuple2<int, int>(
            (seq[(i + gap)] ?? (throw Exception("key not found"))),
            (seq[i] ?? (throw Exception("key not found"))));
        seq[i] = __tmp1.item1;
        seq[(i + gap)] = __tmp1.item2;
        swap = true;
      }
    }
  }
  return seq;
}

main(List<String> argv) {
  List<int> unsorted = [14, 11, 19, 5, 16, 10, 19, 12, 5, 12];
  final List<int> expected = [5, 5, 10, 11, 12, 12, 14, 16, 19, 19];
  assert(DeepCollectionEquality().equals(comb_sort(unsorted), expected));
  print(sprintf("%s", ["OK"]));
}
