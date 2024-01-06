#include <algorithm>  // NOLINT(build/include_order)
#include <cstdint>    // NOLINT(build/include_order)
#include <iostream>   // NOLINT(build/include_order)
#include <vector>     // NOLINT(build/include_order)
int code_0 = 0;
int code_1 = 1;
std::vector<int> l_a = {code_0, code_1};
std::string code_a = std::string{"a"};  // NOLINT(runtime/string)
std::string code_b = std::string{"b"};  // NOLINT(runtime/string)
std::vector<std::string> l_b = {code_a, code_b};
int main(int argc, char** argv) {
  for (auto i : l_a) {
    std::cout << i;
    std::cout << std::endl;
  }
  for (auto j : l_b) {
    std::cout << j;
    std::cout << std::endl;
  }
  if (({
        std::vector<std::string> __tmp1 = {std::string{"a"}, std::string{"b"}};
        (std::find(__tmp1.begin(), __tmp1.end(), std::string{"a"}) !=
         __tmp1.end());
      })) {
    std::cout << std::string{"OK"};
    std::cout << std::endl;
  }
}
