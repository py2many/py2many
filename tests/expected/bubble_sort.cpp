#include "py14/runtime/builtins.h"
#include "py14/runtime/range.hpp"
#include "py14/runtime/sys.h"
#include <cassert>
#include <iostream>
#include <vector>

inline std::vector<int> bubble_sort(std::vector<int> seq) {
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

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::vector<int> unsorted = {14, 11, 19, 5, 16, 10, 19, 12, 5, 12};
  std::vector<int> expected = {5, 5, 10, 11, 12, 12, 14, 16, 19, 19};
  assert(bubble_sort(unsorted) == expected);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
