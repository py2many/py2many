// @dart=3.4
import 'package:sprintf/sprintf.dart';

final int code_0 = 0;
final int code_1 = 1;
final String code_a = "a";
final String code_b = "b";
final Set<String> l_b = new Set.from([code_a]);
final Map<String, int> l_c = {code_b: code_0};
main(List<String> argv) {
  assert(l_b.contains("a"));
  print(sprintf("%s", ["OK"]));
}
