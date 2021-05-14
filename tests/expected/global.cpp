#include "pycpp/runtime/builtins.h"
#include "pycpp/runtime/sys.h"
#include <algorithm>
#include <iostream>
#include <vector>
int code_0 = 0;
int code_1 = 1;
std::vector<int> l_a = {code_0, code_1};
std::string code_a = std::string{"a"};
std::string code_b = std::string{"b"};
std::vector<std::string> l_b = {code_a, code_b};
int main(int argc, char **argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  for (auto i : l_a) {
    std::cout << i;
    std::cout << std::endl;
  }
  for (auto i : l_b) {
    std::cout << i;
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
