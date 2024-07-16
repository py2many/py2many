// @dart=3.4
import 'package:sprintf/sprintf.dart';

compare_assert(int a, int b) {
  assert(a == b);
  assert(!(0 == 1));
}

main(List<String> argv) {
  assert(true);
  assert(!(false));
  compare_assert(1, 1);
  assert(true);
  assert(true);
  print(sprintf("%s", ["OK"]));
}
