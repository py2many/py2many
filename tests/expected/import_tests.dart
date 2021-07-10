// @dart=2.9
import 'package:sprintf/sprintf.dart';

int test() {
  List<int> a = [1, 2, 3];
  return a[1];
}

main(List<String> argv) {
  final int b = test();
  assert(b == 2);
  print(sprintf("%s", ["OK"]));
}
