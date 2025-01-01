import "bar"; // bar1
import "baz"; // baz1
void main(string[] argv) {
  int x = bar1();
  string y = baz1();
  assert(x == 0);
  assert(y == "foo");
}
