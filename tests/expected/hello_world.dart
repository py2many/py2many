// @dart=2.9
import 'package:sprintf/sprintf.dart';

void main() {
  print(sprintf("%s", ["Hello world!"]));
  print(sprintf("%s %s", ["Hello", "world!"]));
}
