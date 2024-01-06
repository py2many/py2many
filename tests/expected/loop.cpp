#include <cppitertools/range.hpp>  // NOLINT(build/include_order)
#include <cstdint>                 // NOLINT(build/include_order)
#include <iostream>                // NOLINT(build/include_order)
inline void for_with_break() {
  for (auto i : iter::range(4)) {
    if (i == 2) {
      break;
    }
    std::cout << i;
    std::cout << std::endl;
  }
}

inline void for_with_continue() {
  for (auto i : iter::range(4)) {
    if (i == 2) {
      continue;
    }
    std::cout << i;
    std::cout << std::endl;
  }
}

inline void for_with_else() {
  bool has_break = false;
  for (auto i : iter::range(4)) {
    std::cout << i;
    std::cout << std::endl;
  }
  if (has_break != true) {
    std::cout << std::string{"OK"};
    std::cout << std::endl;
  }
}

inline void while_with_break() {
  int i = 0;
  while (true) {
    if (i == 2) {
      break;
    }
    std::cout << i;
    std::cout << std::endl;
    i += 1;
  }
}

inline void while_with_continue() {
  int i = 0;
  while (i < 5) {
    i += 1;
    if (i == 2) {
      continue;
    }
    std::cout << i;
    std::cout << std::endl;
  }
}

int main(int argc, char** argv) {
  for_with_break();
  for_with_continue();
  for_with_else();
  while_with_break();
  while_with_continue();
}
