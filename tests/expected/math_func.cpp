#include <cmath>     // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
inline void main_func() {
  int a = std::pow(2, 4);
  std::cout << a;
  std::cout << std::endl;
}

int main(int argc, char** argv) { main_func(); }
