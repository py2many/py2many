// @dart=3.4
import 'package:sprintf/sprintf.dart';

main(List<String> argv) {
  print(sprintf("%s", ["Hello world!"]));
  print(sprintf("%s %s", ["Hello", "world!"]));
}
