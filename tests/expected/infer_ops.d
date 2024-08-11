// generated by py2many --dlang=1
import std;

void foo() {
  int a = 10;
  int b = 20;
  int _c1 = (a + b);
  int _c2 = (a - b);
  int _c3 = (a * b);
  int _c4 = (a / b);
  int _c5 = -(a);
  double d = 2.0;
  double _e1 = (a + d);
  double _e2 = (a - d);
  double _e3 = (a * d);
  double _e4 = (a / d);
  double _f = -3.0;
  int _g = -(a);
}

short add1(byte x, byte y) {
  return (x + y);
}

int add2(short x, short y) {
  return (x + y);
}

long add3(int x, int y) {
  return (x + y);
}

long add4(long x, long y) {
  return (x + y);
}

ushort add5(ubyte x, ubyte y) {
  return (x + y);
}

uint add6(ushort x, ushort y) {
  return (x + y);
}

ulong add7(uint x, uint y) {
  return (x + y);
}

ulong add8(ulong x, ulong y) {
  return (x + y);
}

uint add9(byte x, ushort y) {
  return (x + y);
}

byte sub(byte x, byte y) {
  return (x - y);
}

short mul(byte x, byte y) {
  return (x * y);
}

double fadd1(byte x, double y) {
  return (x + y);
}

void show() {
  assert(fadd1(6, 6.0) == 12);
  writeln(format("%s", "OK"));
}

void main(string[] argv) {
  foo();
  show();
}
