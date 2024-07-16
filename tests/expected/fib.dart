// @dart=3.4
import 'package:sprintf/sprintf.dart';

int fib(int i) {
  if (i == 0 || i == 1) {
    return 1;
  }
  return (fib((i - 1)) + fib((i - 2)));
}

main(List<String> argv) {
  print(sprintf("%s", [fib(5)]));
}
