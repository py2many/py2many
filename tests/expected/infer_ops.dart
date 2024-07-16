// @dart=3.4
import 'package:sprintf/sprintf.dart';

foo() {
  final int a = 10;
  final int b = 20;
  final int _c1 = (a + b);
  final int _c2 = (a - b);
  final int _c3 = (a * b);
  final int _c4 = (a ~/ b);
  final int _c5 = -(a);
  final double d = 2.0;
  final double _e1 = (a + d);
  final double _e2 = (a - d);
  final double _e3 = (a * d);
  final double _e4 = (a / d);
  final double _f = -3.0;
  final int _g = -(a);
}

int add1(int x, int y) {
  return (x + y);
}

int add2(int x, int y) {
  return (x + y);
}

int add3(int x, int y) {
  return (x + y);
}

int add4(int x, int y) {
  return (x + y);
}

int add5(int x, int y) {
  return (x + y);
}

int add6(int x, int y) {
  return (x + y);
}

int add7(int x, int y) {
  return (x + y);
}

int add8(int x, int y) {
  return (x + y);
}

int add9(int x, int y) {
  return (x + y);
}

int sub(int x, int y) {
  return (x - y);
}

int mul(int x, int y) {
  return (x * y);
}

double fadd1(int x, double y) {
  return (x + y);
}

show() {
  assert(fadd1(6, 6.0) == 12);
  print(sprintf("%s", ["OK"]));
}

main(List<String> argv) {
  foo();
  show();
}
