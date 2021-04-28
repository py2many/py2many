// @dart=2.9
import 'package:sprintf/sprintf.dart';

show() {
  print(sprintf("%s", ["b"]));
  print(sprintf("%s %s", [2, "b"]));
  double a = 2.1;
  print(sprintf("%s", [a]));
  final double b = 2.1;
  print(sprintf("%s", [b]));
}

main() {
  show();
}
