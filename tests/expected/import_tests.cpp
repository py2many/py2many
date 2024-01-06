#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
#include <vector>    // NOLINT(build/include_order)

inline int test() {
  std::vector<int> a = {1, 2, 3};
  return a[1];
}

int main(int argc, char** argv) {
  int b = test();
  assert(b == 2);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
