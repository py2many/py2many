// @dart=2.9
import 'package:sprintf/sprintf.dart';

int code_0 = 0;
int code_1 = 1;
var l_a = [code_0, code_1];
String code_a = "a";
String code_b = "b";
var l_b = [code_a, code_b];
main() {
  for (final i in l_a) {
    print(sprintf("%s", [i]));
  }
  for (final i in l_b) {
    print(sprintf("%s", [i]));
  }

  if (["a", "b"].contains("a")) {
    print(sprintf("%s", ["OK"]));
  }
}
