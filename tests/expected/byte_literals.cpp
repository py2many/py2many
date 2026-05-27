#include <array>     // NOLINT(build/include_order)
#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
#include <string>    // NOLINT(build/include_order)
int main(int argc, char** argv) {
  assert(((std::array<unsigned char, 3>){0x66, 0x6f, 0x6f}) !=
         ((std::array<unsigned char, 3>){0x62, 0x61, 0x72}));
  assert(((std::array<unsigned char, 1>){0x22}) ==
         ((std::array<unsigned char, 1>){0x22}));
  assert(((std::array<unsigned char, 1>){0x27}) ==
         ((std::array<unsigned char, 1>){0x27}));
  assert(((std::array<unsigned char, 4>){0xbb, 0x66, 0x6f, 0x6f}) ==
         ((std::array<unsigned char, 4>){0xbb, 0x66, 0x6f, 0x6f}));
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
