// @dart=3.4
import 'package:sprintf/sprintf.dart';

class Foo {
  int bar() {
    return baz();
  }

  int baz() {
    return 10;
  }
}

main(List<String> argv) {
  final Foo f = Foo();
  final b = f.bar();
  print(sprintf("%s", [b]));
  assert(b == 10);
}
