// @dart=2.9
import 'package:sprintf/sprintf.dart';

int code_0 = 0;
int code_1 = 1;
String code_a = "a";
String code_b = "b";
var l_b = new Set.from([code_a]);
var l_c = {code_b: code_0};
void main() {
  assert(l_b.contains("a"));
  print(sprintf("%s", ["OK"]));
}
