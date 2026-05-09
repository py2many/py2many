#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
inline void show() {
  auto f = [](auto x) { return x + 1; };
  std::cout << f(5);
  std::cout << std::endl;
}

int main(int argc, char** argv) { show(); }
