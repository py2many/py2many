// @dart=2.9
import 'package:sprintf/sprintf.dart';

main_func() {
  List<bool> ands = [];
  List<bool> ors = [];
  List<bool> xors = [];
  for (final a in [false, true]) {
    for (final b in [false, true]) {
      ands.add((a & b));
      ors.add((a | b));
      xors.add((a ^ b));
    }
  }
  assert(ands == [false, false, false, true]);
  assert(ors == [false, true, true, true]);
  assert(xors == [false, true, true, false]);
  print(sprintf("%s", ["OK"]));
}

main() {
  main_func();
}
