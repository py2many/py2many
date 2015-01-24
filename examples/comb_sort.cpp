#include "sys.h"
#include "builtins.h"
#include <iostream>
#include <string>
#include <algorithm>
#include <cmath>
#include <vector>
#include <tuple>
#include <utility>
using namespace std::literals::string_literals;
auto sort = [](auto seq) {
  auto gap = py14::len(seq);
  auto swap = true;
  while (gap > 1 || swap) {
    gap = std::max(1, py14::to_int(gap / 1.25));
    swap = false;
    for (auto i : py14::range(py14::len(seq) - gap)) {
      if (seq[i] > seq[i + gap]) {
        std::tie(seq[i], seq[i + gap]) = std::make_tuple(seq[i + gap], seq[i]);
        swap = true;
        return seq;
      }
    }
  }
};
int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::vector<decltype(10)> unsorted{10, 6, 1, 0, 2, 3, 5, 1, 6, 2};
  auto sorted = sort(unsorted);
  for (auto n : sorted) {
    std::cout << n << std::endl;
  }
}
