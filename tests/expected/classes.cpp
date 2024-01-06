#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
class Foo {
 public:
  inline int bar() { return this->baz(); }

  inline int baz() { return 10; }
};

int main(int argc, char** argv) {
  Foo f = Foo();
  auto b = f.bar();
  std::cout << b;
  std::cout << std::endl;
  assert(b == 10);
}
