#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
inline void compare_assert(int a, int b) {
  assert(a == b);
  assert(!(0 == 1));
}

int main(int argc, char** argv) {
  assert(true);
  assert(!(false));
  compare_assert(1, 1);
  assert(true);
  assert(true);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
