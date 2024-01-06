#include <algorithm>  // NOLINT(build/include_order)
#include <cstdint>    // NOLINT(build/include_order)
#include <iostream>   // NOLINT(build/include_order)
#include <map>        // NOLINT(build/include_order)
#include <vector>     // NOLINT(build/include_order)
inline bool nested_containers() {
  std::map<std::string, std::vector<int>> CODES =
      std::map<std::string, std::vector<int>>{{std::string{"KEY"}, {1, 3}}};
  return (std::find(CODES[std::string{"KEY"}].begin(),
                    CODES[std::string{"KEY"}].end(),
                    1) != CODES[std::string{"KEY"}].end());
}

int main(int argc, char** argv) {
  if (nested_containers()) {
    std::cout << std::string{"OK"};
    std::cout << std::endl;
  }
}
