#include "pycpp/runtime/builtins.h"
#include "pycpp/runtime/sys.h"
#include <cassert>
#include <iostream>
#include <vector>

inline void main_func() {
  std::vector<bool> ands = {};
  std::vector<bool> ors = {};
  std::vector<bool> xors = {};
  for (auto a : std::vector<bool>{false, true}) {
    for (auto b : std::vector<bool>{false, true}) {
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

int main(int argc, char **argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  main_func();
}
