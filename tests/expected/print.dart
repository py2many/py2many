// @dart=2.9
import 'package:sprintf/sprintf.dart';

main() {
  print(sprintf("%s", [2]));
  print(sprintf("%s", ["b"]));
  print(sprintf("%s %s", [2, "b"]));
}
