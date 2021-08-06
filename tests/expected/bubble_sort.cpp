#include <cassert>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
#include <tuple>
#include <vector>  // NOLINT(build/include_order)

#include "pycpp/runtime/builtins.h"  // NOLINT(build/include_order)
#include "pycpp/runtime/range.hpp"   // NOLINT(build/include_order)
#include "pycpp/runtime/sys.h"       // NOLINT(build/include_order)

inline std::vector<int> bubble_sort(std::vector<int>& seq) {
  auto L = seq.size();
  for (auto _ : rangepp::xrange(L)) {
    for (auto n : rangepp::xrange(1, L)) {
      if (seq[n] < seq[n - 1]) {
        std::tie(seq[n - 1], seq[n]) = std::make_tuple(seq[n], seq[n - 1]);
      }
    }
  }
  return seq;
}

int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::vector<int> unsorted = {14, 11, 19, 5, 16, 10, 19, 12, 5, 12};
  std::vector<int> expected = {5, 5, 10, 11, 12, 12, 14, 16, 19, 19};
  assert(bubble_sort(unsorted) == expected);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
