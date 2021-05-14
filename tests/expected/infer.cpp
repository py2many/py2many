#include "pycpp/runtime/builtins.h"
#include "pycpp/runtime/sys.h"
#include <cassert>
#include <iostream>
inline void foo() {
  int a = 10;
  int b = a;
  assert(b == 10);
  std::cout << b;
  std::cout << std::endl;
}

int main(int argc, char **argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  foo();
}
