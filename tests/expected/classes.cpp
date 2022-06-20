#include <cassert>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)

#include "pycpp/runtime/sys.h"  // NOLINT(build/include_order)
class Foo {
 public:
  inline int bar() { return this->baz(); }

  inline int baz() { return 10; }
};

int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  Foo f = Foo();
  auto b = f.bar();
  std::cout << b;
  std::cout << std::endl;
  assert(b == 10);
}
