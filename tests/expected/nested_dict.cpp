#include "pycpp/runtime/builtins.h"
#include "pycpp/runtime/sys.h"
#include <algorithm>
#include <iostream>
#include <map>
#include <vector>
inline bool nested_containers() {
  std::map<std::string, std::vector<int>> CODES =
      std::map<std::string, std::vector<int>>{
          {std::string{"KEY"}, std::vector<int>{1, 3}}};
  return (std::find(CODES[std::string{"KEY"}].begin(),
                    CODES[std::string{"KEY"}].end(),
                    1) != CODES[std::string{"KEY"}].end());
}

int main(int argc, char **argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  if (nested_containers()) {
    std::cout << std::string{"OK"};
    std::cout << std::endl;
  }
}
