#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
#include <vector>    // NOLINT(build/include_order)

inline void main_func() {
  std::vector<bool> ands = {};
  std::vector<bool> ors = {};
  std::vector<bool> xors = {};
  for (auto a : {false, true}) {
    for (auto b : {false, true}) {
      ands.push_back(a & b);
      ors.push_back(a | b);
      xors.push_back(a ^ b);
    }
  }
  assert(({
    std::vector<bool> __tmp1 = {false, false, false, true};
    ands == __tmp1;
  }));
  assert(({
    std::vector<bool> __tmp2 = {false, true, true, true};
    ors == __tmp2;
  }));
  assert(({
    std::vector<bool> __tmp3 = {false, true, true, false};
    xors == __tmp3;
  }));
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}

int main(int argc, char** argv) { main_func(); }
