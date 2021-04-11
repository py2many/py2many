// @dart=2.9
import 'package:sprintf/sprintf.dart';

main() {
  print(sprintf("%s \n", [2]));
  print(sprintf("%s \n", ["b"]));
  print(sprintf("%s %s \n", [2, "b"]));
}
