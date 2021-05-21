#include <cassert>
#include <iostream>

#include "pycpp/runtime/builtins.h"
#include "pycpp/runtime/sys.h"
inline void compare_assert(int a, int b) {
  assert(a == b);
  assert(!(0 == 1));
}

int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  assert(true);
  assert(!(false));
  compare_assert(1, 1);
  assert(true);
  assert(true);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
