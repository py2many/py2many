// @dart=2.9
import 'package:sprintf/sprintf.dart';

final int code_0 = 0;
final int code_1 = 1;
final l_a = [code_0, code_1];
final String code_a = "a";
final String code_b = "b";
final l_b = [code_a, code_b];
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
