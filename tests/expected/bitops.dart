// @dart=3.4
import 'package:collection/collection.dart';
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
  assert(DeepCollectionEquality().equals(ands, [false, false, false, true]));
  assert(DeepCollectionEquality().equals(ors, [false, true, true, true]));
  assert(DeepCollectionEquality().equals(xors, [false, true, true, false]));
  print(sprintf("%s", ["OK"]));
}

main(List<String> argv) {
  main_func();
}
