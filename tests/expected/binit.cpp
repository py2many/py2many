#include "py14/runtime/builtins.h"
#include "py14/runtime/sys.h"
#include <cassert>

template <typename T1, typename T2> auto bisect_right(T1 data, T2 item) {
  int low = 0;
  int high = py14::to_int(data.size());
  while (low < high) {
    auto middle = py14::to_int((low + high) / 2);
    if (item < data[middle]) {
      high = middle;
    } else {
      low = middle + 1;
    }
  }
  return low;
}

template <typename T1, typename T2> auto bin_it(T1 limits, T2 data) {
  std::vector<decltype(0)> bins{0};
  for (auto _x : limits) {
    bins.push_back(0);
  }
  for (auto d : data) {
    bins[bisect_right(limits, d)] += 1;
  }
  return bins;
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::vector<decltype(23)> limits{23, 37, 43, 53, 67, 83};
  std::vector<decltype(95)> data{
      95, 21, 94, 12, 99, 4,  70, 75, 83, 93, 52, 80, 57, 5,  53, 86, 65,
      17, 92, 83, 71, 61, 54, 58, 47, 16, 8,  9,  32, 84, 7,  87, 46, 19,
      30, 37, 96, 6,  98, 40, 79, 97, 45, 64, 60, 29, 49, 36, 43, 55};
  assert(({
    std::vector<decltype(11)> __tmp1{11, 4, 2, 6, 9, 5, 13};
    bin_it(limits, data) == __tmp1;
  }));
}
