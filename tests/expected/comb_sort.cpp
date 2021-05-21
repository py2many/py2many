#include <math.h>

#include <cassert>
#include <iostream>
#include <tuple>
#include <vector>

#include "pycpp/runtime/builtins.h"
#include "pycpp/runtime/range.hpp"
#include "pycpp/runtime/sys.h"

inline std::vector<int> comb_sort(std::vector<int> seq) {
  auto gap = seq.size();
  bool swap = true;
  while (gap > 1 || swap) {
    gap = std::max(static_cast<size_t>(1),
                   static_cast<size_t>(floor(gap / 1.25)));
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

int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::vector<int> unsorted = {14, 11, 19, 5, 16, 10, 19, 12, 5, 12};
  std::vector<int> expected = {5, 5, 10, 11, 12, 12, 14, 16, 19, 19};
  assert(comb_sort(unsorted) == expected);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
