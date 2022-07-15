// @dart=2.9
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
