// @dart=2.9
import 'package:sprintf/sprintf.dart';

int indexing() {
  int sum = 0;
  List<int> a = [];
  for (final i in ([for (var i = 0; i < 10; i += 1) i])) {
    a.add(i);
    sum += a[i];
  }
  return sum;
}

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
  int sum1 = indexing();
  print(sprintf("%s", [sum1]));
  var a5 = [1, 2, 3];
  print(sprintf("%s", [a5.length]));
}

void main() {
  show();
}
