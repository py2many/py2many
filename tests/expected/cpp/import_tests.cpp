#include <cassert>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
#include <vector>    // NOLINT(build/include_order)

#include "pycpp/runtime/builtins.h"  // NOLINT(build/include_order)
#include "pycpp/runtime/sys.h"       // NOLINT(build/include_order)

inline int test() {
  std::vector<int> a = {1, 2, 3};
  return a[1];
}

int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  int b = test();
  assert(b == 2);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
