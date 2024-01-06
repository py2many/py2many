#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
inline int fib(int i) {
  if (i == 0 || i == 1) {
    return 1;
  }
  return (fib(i - 1)) + (fib(i - 2));
}

int main(int argc, char** argv) {
  std::cout << fib(5);
  std::cout << std::endl;
}
