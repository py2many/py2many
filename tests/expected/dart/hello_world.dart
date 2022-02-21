// @dart=2.9
import 'package:sprintf/sprintf.dart';

main(List<String> argv) {
  print(sprintf("%s", ["Hello world!"]));
  print(sprintf("%s %s", ["Hello", "world!"]));
}
