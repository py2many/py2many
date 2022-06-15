#include <iostream>  // NOLINT(build/include_order)

#include "pycpp/runtime/builtins.h"  // NOLINT(build/include_order)
#include "pycpp/runtime/sys.h"       // NOLINT(build/include_order)

int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
  exit(1);
}
