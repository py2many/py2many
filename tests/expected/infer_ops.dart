// @dart=2.9
import 'package:sprintf/sprintf.dart';

foo() {
  final int a = 10;
  final int b = 20;
  final int c1 = (a + b);
  final int c2 = (a - b);
  final int c3 = (a * b);
  final double c4 = (a / b);
  final int c5 = -(a);
  final double d = 2.0;
  final double e1 = (a + d);
  final double e2 = (a - d);
  final double e3 = (a * d);
  final double e4 = (a / d);
  final double f = -3.0;
  final int g = -(a);
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
  final double rv = fadd1(6, 6.0);
  assert(rv == 12);
  print(sprintf("%s", ["OK"]));
}

main() {
  foo();
  show();
}
