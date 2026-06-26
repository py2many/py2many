// @dart=3.4
import 'dart:math';
import 'package:sprintf/sprintf.dart';

main_func() {
  final int a = (pow(2, 4) as int);
  print(sprintf("%s", [a]));
}

main(List<String> argv) {
  main_func();
}
