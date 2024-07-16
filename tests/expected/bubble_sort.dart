// @dart=3.4
import 'package:collection/collection.dart';
import 'package:sprintf/sprintf.dart';
import 'package:tuple/tuple.dart';

List<int> bubble_sort(List<int> seq) {
  final L = seq.length;
  for (final _ in ([for (var i = 0; i < L; i += 1) i])) {
    for (final n in ([for (var i = 1; i < L; i += 1) i])) {
      if ((seq[n] ?? (throw Exception("key not found"))) <
          (seq[(n - 1)] ?? (throw Exception("key not found")))) {
        final __tmp1 = Tuple2<int, int>(
            (seq[n] ?? (throw Exception("key not found"))),
            (seq[(n - 1)] ?? (throw Exception("key not found"))));
        seq[(n - 1)] = __tmp1.item1;
        seq[n] = __tmp1.item2;
      }
    }
  }
  return seq;
}

main(List<String> argv) {
  List<int> unsorted = [14, 11, 19, 5, 16, 10, 19, 12, 5, 12];
  final List<int> expected = [5, 5, 10, 11, 12, 12, 14, 16, 19, 19];
  assert(DeepCollectionEquality().equals(bubble_sort(unsorted), expected));
  print(sprintf("%s", ["OK"]));
}
