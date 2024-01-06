#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
#include <vector>    // NOLINT(build/include_order)

inline int bisect_right(std::vector<int>& data, int item) {
  int low = 0;
  int high = static_cast<int>(static_cast<int>(data.size()));
  while (low < high) {
    int middle = static_cast<int>((low + high) / 2);
    if (item < data[middle]) {
      high = middle;
    } else {
      low = middle + 1;
    }
  }
  return low;
}

inline std::vector<int> bin_it(std::vector<int>& limits,
                               std::vector<int>& data) {
  std::vector<int> bins = {0};
  for (auto _x : limits) {
    bins.push_back(0);
  }
  for (auto d : data) {
    bins[bisect_right(limits, d)] += 1;
  }
  return bins;
}

int main(int argc, char** argv) {
  std::vector<int> limits = {23, 37, 43, 53, 67, 83};
  std::vector<int> data = {95, 21, 94, 12, 99, 4,  70, 75, 83, 93, 52, 80, 57,
                           5,  53, 86, 65, 17, 92, 83, 71, 61, 54, 58, 47, 16,
                           8,  9,  32, 84, 7,  87, 46, 19, 30, 37, 96, 6,  98,
                           40, 79, 97, 45, 64, 60, 29, 49, 36, 43, 55};
  assert(({
    std::vector<int> __tmp1 = {11, 4, 2, 6, 9, 5, 13};
    bin_it(limits, data) == __tmp1;
  }));
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
