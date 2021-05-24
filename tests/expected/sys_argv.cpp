#include <cassert>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)

#include "pycpp/runtime/builtins.h"  // NOLINT(build/include_order)
#include "pycpp/runtime/sys.h"       // NOLINT(build/include_order)

int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::vector<std::string> a = pycpp::sys::argv;
  std::string cmd = a[0];
  assert(cmd.find(std::string{"sys_argv"}) != std::string::npos);
  if (a.size() > 1) {
    std::cout << a[1];
    std::cout << std::endl;
  } else {
    std::cout << std::string{"OK"};
    std::cout << std::endl;
  }
}
