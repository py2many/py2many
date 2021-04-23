#include "py14/runtime/builtins.h"
#include "py14/runtime/sys.h"
#include <iostream>

inline void show() {
  auto myfunc = [](auto x, auto y) { return x + y; };
  std::cout << myfunc(1, 2);
  std::cout << std::endl;
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  show();
}
