// @dart=2.9
import 'package:sprintf/sprintf.dart';

foo() {
  int a = 10;
  int b = 20;
  int c1 = (a + b);
  int c2 = (a - b);
  int c3 = (a * b);
  double c4 = (a / b);
  int c5 = -(a);
  double d = 2.0;
  double e1 = (a + d);
  double e2 = (a - d);
  double e3 = (a * d);
  double e4 = (a / d);
  double f = -3.0;
  int g = -(a);
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
  double rv = fadd1(6, 6.0);
  assert(rv == 12);
  print(sprintf("%s", ["OK"]));
}

main() {
  foo();
  show();
}
