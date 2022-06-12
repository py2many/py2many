#include <iostream>  // NOLINT(build/include_order)

#include "pycpp/runtime/builtins.h"  // NOLINT(build/include_order)
#include "pycpp/runtime/sys.h"       // NOLINT(build/include_order)

inline void main_func() {
  int16_t a = static_cast<int16_t>(1);
  auto b = a;
  std::cout << b;
  std::cout << std::endl;
  int64_t c = static_cast<int64_t>(1);
  auto d = c;
  std::cout << d;
  std::cout << std::endl;
  uint64_t e = static_cast<uint64_t>(1);
  auto f = e;
  std::cout << f;
  std::cout << std::endl;
}

int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  main_func();
}
