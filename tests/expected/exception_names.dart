// @dart=3.4
import 'package:sprintf/sprintf.dart';

show() {
  try {
    (3 ~/ 0);
  } on IntegerDivisionByZeroException {
    print(sprintf("%s", ["ZeroDivisionError"]));
  }
}

main(List<String> argv) {
  show();
}
