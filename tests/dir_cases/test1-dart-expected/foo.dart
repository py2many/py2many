import "bar"; // bar1
import "baz"; // baz1

main(List<String> argv) {
  final int x = bar1();
  final String y = baz1();
  assert(x == 0);
  assert(y == "foo");
}
