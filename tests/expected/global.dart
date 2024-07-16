// @dart=3.4
import 'package:sprintf/sprintf.dart';

final int code_0 = 0;
final int code_1 = 1;
final List<int> l_a = [code_0, code_1];
final String code_a = "a";
final String code_b = "b";
final List<String> l_b = [code_a, code_b];
main(List<String> argv) {
  for (final i in l_a) {
    print(sprintf("%s", [i]));
  }
  for (final j in l_b) {
    print(sprintf("%s", [j]));
  }

  if (["a", "b"].contains("a")) {
    print(sprintf("%s", ["OK"]));
  }
}
