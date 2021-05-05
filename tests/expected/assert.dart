// @dart=2.9
import 'package:sprintf/sprintf.dart';

compare_assert(int a, int b) {
  assert(a == b);
  assert(!(0 == 1));
}

main() {
  assert(true);
  assert(!(false));
  compare_assert(1, 1);
  assert(true);
  assert(true);
  print(sprintf("%s", ["OK"]));
}
