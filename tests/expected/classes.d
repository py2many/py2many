// generated by py2many --d=1
import std;

class Foo {

  int bar() {
    return baz();
  }

  int baz() {
    return 10;
  }

}

void main(string[] argv) {
  Foo f = new Foo();
  auto b = f.bar();
  writeln(format("%s", b));
  assert(b == 10);
}
