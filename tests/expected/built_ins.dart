// @dart=2.9
import 'dart:math';
import 'package:sprintf/sprintf.dart';

main(List<String> argv) {
  final int a = max(1, 2);
  print(sprintf("%s", [a]));
  final int b = min(1, 2);
  print(sprintf("%s", [b]));
}
