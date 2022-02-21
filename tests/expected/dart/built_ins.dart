// @dart=2.9
import 'dart:math';
import 'package:sprintf/sprintf.dart';

default_builtins() {
  final String a = "";
  final bool b = false;
  final int c = 0;
  assert(a == "");
  assert(b == false);
  assert(c == 0);
}

main(List<String> argv) {
  final int a = max(1, 2);
  print(sprintf("%s", [a]));
  final int b = min(1, 2);
  print(sprintf("%s", [b]));
}
