// @dart=2.9
import 'package:sprintf/sprintf.dart';

show() {
  try {
    throw new Exception("foo");
  } on Exception catch (e) {
    print(sprintf("%s", ["caught"]));
  } finally {
    print(sprintf("%s", ["Finally"]));
  }
  try {
    (3 ~/ 0);
  } on IntegerDivisionByZeroException {
    print(sprintf("%s", ["OK"]));
  }
  try {
    throw new Exception("foo");
  } catch (e) {
    print(sprintf("%s", ["Got it"]));
  }
}

main() {
  show();
}
