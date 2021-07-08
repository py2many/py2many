// @dart=2.9
import 'package:sprintf/sprintf.dart';

class Foo {
  String bar() {
    return "a";
  }
}

main(List<String> argv) {
  final Foo f = Foo();
  final b = f.bar();
  print(sprintf("%s", [b]));
}
