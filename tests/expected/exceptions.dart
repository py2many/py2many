// @dart=3.4
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
    throw new Exception("foo");
  } catch (e) {
    print(sprintf("%s", ["Got it"]));
  }
  try {
    throw new Exception("foo");
  } on Exception catch (e) {
    assert(e.toString().contains("foo"));
  }
}

main(List<String> argv) {
  show();
}
