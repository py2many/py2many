#include "py14/runtime/builtins.h"
#include "py14/runtime/sys.h"
#include <cassert>
#include <iostream>
inline void compare_assert(int a, int b) {
  assert(a == b);
  assert(!(0 == 1));
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  compare_assert(1, 1);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
