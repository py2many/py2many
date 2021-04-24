#include "py14/runtime/builtins.h"
#include "py14/runtime/range.hpp"
#include "py14/runtime/sys.h"
#include <cassert>
#include <iostream>

inline std::vector<int> comb_sort(std::vector<int> seq) {
  auto gap = seq.size();
  bool swap = true;
  while (gap > 1 || swap) {
    gap = std::max(1, py14::to_int(gap / 1.25));
    swap = false;
    for (auto i : rangepp::xrange((seq.size()) - gap)) {
      if (seq[i] > seq[i + gap]) {
        std::tie(seq[i], seq[i + gap]) = std::make_tuple(seq[i + gap], seq[i]);
        swap = true;
      }
    }
  }
  return seq;
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::vector<decltype(14)> unsorted{14, 11, 19, 5, 16, 10, 19, 12, 5, 12};
  std::vector<decltype(5)> expected{5, 5, 10, 11, 12, 12, 14, 16, 19, 19};
  assert(comb_sort(unsorted) == expected);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
