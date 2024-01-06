#include <algorithm>  // NOLINT(build/include_order)
#include <cstdint>    // NOLINT(build/include_order)
#include <iostream>   // NOLINT(build/include_order)
#include <vector>     // NOLINT(build/include_order)
inline void show() {
  int a = 1;
  auto b = (({
    std::vector<int> __tmp1 = {2, 3};
    (std::find(__tmp1.begin(), __tmp1.end(), a) != __tmp1.end());
  })
                ? ({ 2; })
                : ({ 3; }));
  std::cout << b;
  std::cout << std::endl;
}

int main(int argc, char** argv) { show(); }
