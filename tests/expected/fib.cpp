#include "pycpp/runtime/builtins.h"
#include "pycpp/runtime/sys.h"
#include <iostream>
inline int fib(int i) {
  if (i == 0 || i == 1) {
    return 1;
  }
  return (fib(i - 1)) + (fib(i - 2));
}

int main(int argc, char **argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  int rv = fib(5);
  std::cout << rv;
  std::cout << std::endl;
}
