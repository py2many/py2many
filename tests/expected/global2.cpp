#include <algorithm>  // NOLINT(build/include_order)
#include <cassert>    // NOLINT(build/include_order)
#include <cstdint>    // NOLINT(build/include_order)
#include <iostream>   // NOLINT(build/include_order)
#include <map>        // NOLINT(build/include_order)
#include <set>        // NOLINT(build/include_order)
int code_0 = 0;
int code_1 = 1;
std::string code_a = std::string{"a"};  // NOLINT(runtime/string)
std::string code_b = std::string{"b"};  // NOLINT(runtime/string)
std::set<std::string> l_b = std::set<std::string>{code_a};
std::map<std::string, int> l_c = std::map<std::string, int>{{code_b, code_0}};
int main(int argc, char** argv) {
  assert((std::find(l_b.begin(), l_b.end(), std::string{"a"}) != l_b.end()));
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}
