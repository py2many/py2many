// @dart=3.4
import 'package:sprintf/sprintf.dart';

show() {
  final f = (x) => (x + 1);
  print(sprintf("%s", [f(5)]));
}

main(List<String> argv) {
  show();
}
