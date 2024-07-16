// @dart=3.4
import 'package:sprintf/sprintf.dart';

show() {
  var myfunc = (x, y) => (x + y);
  print(sprintf("%s", [myfunc(1, 2)]));
}

main(List<String> argv) {
  show();
}
