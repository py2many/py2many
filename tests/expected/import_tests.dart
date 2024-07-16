// @dart=3.4
import 'package:sprintf/sprintf.dart';

int test() {
  List<int> a = [1, 2, 3];
  return (a[1] ?? (throw Exception("key not found")));
}

main(List<String> argv) {
  final int b = test();
  assert(b == 2);
  print(sprintf("%s", ["OK"]));
}
