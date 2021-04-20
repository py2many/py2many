// @dart=2.9
import 'package:sprintf/sprintf.dart';

show() {
  int a1 = 10;
  double a2 = 2.1;
  print(sprintf("%s", [a2]));
  for (final i in ([for (var i = 0; i < 10; i += 1) i])) {
    print(sprintf("%s", [i]));
  }
  for (final i in ([for (var i = 0; i < 10; i += 2) i])) {
    print(sprintf("%s", [i]));
  }
  int a3 = -(a1);
  int a4 = (a3 + a1);
  print(sprintf("%s", [a4]));
}

void main() {
  show();
}
