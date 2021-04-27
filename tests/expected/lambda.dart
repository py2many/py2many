// @dart=2.9
import 'package:sprintf/sprintf.dart';

show() {
  var myfunc = (x, y) => (x + y);
  print(sprintf("%s", [myfunc(1, 2)]));
}

main() {
  show();
}
