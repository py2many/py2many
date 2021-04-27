// @dart=2.9
import 'package:sprintf/sprintf.dart';

foo() {
  int a = 10;
  int b = a;
  assert(b == 10);
  print(sprintf("%s", [b]));
}

main() {
  foo();
}
