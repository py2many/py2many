// @dart=2.9
import 'package:sprintf/sprintf.dart';

int fib(int i) {
  if (i == 0 || i == 1) {
    return 1;
  }
  return (fib((i - 1)) + fib((i - 2)));
}

main() {
  int rv = fib(5);
  print(sprintf("%s", [rv]));
}
