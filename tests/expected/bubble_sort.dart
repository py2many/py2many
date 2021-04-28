// @dart=2.9
import 'package:sprintf/sprintf.dart';
import 'package:tuple/tuple.dart';

List<int> bubble_sort(List<int> seq) {
  final L = seq.length;
  for (final _ in ([for (var i = 0; i < L; i += 1) i])) {
    for (final n in ([for (var i = 1; i < L; i += 1) i])) {
      if (seq[n] < seq[(n - 1)]) {
        {
          final t = Tuple2<int, int>(seq[n], seq[(n - 1)]);
          seq[(n - 1)] = __tmp1;
          seq[n] = __tmp2;
        }
      }
    }
  }
  return seq;
}

main() {
  var unsorted = [14, 11, 19, 5, 16, 10, 19, 12, 5, 12];
  final expected = [5, 5, 10, 11, 12, 12, 14, 16, 19, 19];
  assert(bubble_sort(unsorted) == expected);
  print(sprintf("%s", ["OK"]));
}
