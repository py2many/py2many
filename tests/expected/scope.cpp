#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
int global_var = 10;
inline void test_global() {
  global_var = 20;
  std::cout << global_var;
  std::cout << std::endl;
}

inline void show() { test_global(); }

int main(int argc, char** argv) { show(); }
