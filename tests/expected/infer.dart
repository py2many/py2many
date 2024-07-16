// @dart=3.4
import 'package:sprintf/sprintf.dart';

foo() {
  final int a = 10;
  final int b = a;
  assert(b == 10);
  print(sprintf("%s", [b]));
}

main(List<String> argv) {
  foo();
}
