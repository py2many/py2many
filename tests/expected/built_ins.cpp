#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
inline void default_builtins() {
  std::string a = "";
  bool b = false;
  int c = int();
  double d = float();
  assert(a == std::string{""});
  assert(b == false);
  assert(c == 0);
  assert(d == 0.0);
}

int main(int argc, char** argv) {
  int a = std::max(1, 2);
  std::cout << a;
  std::cout << std::endl;
  int b = std::min(1, 2);
  std::cout << b;
  std::cout << std::endl;
  int c = static_cast<int>(std::min(1.0, 2.0));
  std::cout << c;
  std::cout << std::endl;
}
