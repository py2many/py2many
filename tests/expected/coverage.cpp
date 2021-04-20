#include "py14/runtime/builtins.h"
#include "py14/runtime/range.hpp"
#include "py14/runtime/sys.h"
#include <iostream>
inline void show() {
  int a1 = 10;
  double a2 = 2.1;
  std::cout << a2;
  std::cout << std::endl;
  for (auto i : rangepp::xrange(0, 10)) {
    std::cout << i;
    std::cout << std::endl;
  }
  for (auto i : rangepp::xrange(0, 10, 2)) {
    std::cout << i;
    std::cout << std::endl;
  }
  int a3 = -(a1);
  int a4 = a3 + a1;
  std::cout << a4;
  std::cout << std::endl;
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  show();
}
