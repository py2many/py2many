// generated by py2many --dlang=1
import std;

int test() {
  int[] a = [1, 2, 3];
  return a[1];
}

void main(string[] argv) {
  int b = test();
  assert(b == 2);
  writeln(format("%s", "OK"));
}
