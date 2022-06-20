#include <iostream>  // NOLINT(build/include_order)

#include "pycpp/runtime/sys.h"  // NOLINT(build/include_order)
int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::cout << std::string{"Hello world!"};
  std::cout << std::endl;
  std::cout << std::string{"Hello"};
  std::cout << " ";
  std::cout << std::string{"world!"};
  std::cout << std::endl;
}
