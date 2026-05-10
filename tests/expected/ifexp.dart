// @dart=3.4
import 'package:sprintf/sprintf.dart';

show() {
  final int a = 1;
  final b = [2, 3].contains(a) ? (2) : (3);
  print(sprintf("%s", [b]));
}

main(List<String> argv) {
  show();
}
