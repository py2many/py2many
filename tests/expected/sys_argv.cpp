#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
#include <string>    // NOLINT(build/include_order)
#include <vector>    // NOLINT(build/include_order)

int main(int argc, char** argv) {
  std::vector<std::string> a = std::vector<std::string>(argv, argv + argc);
  std::string cmd = a[0];
  if (cmd == std::string{"dart"}) {
    /* pass */
  } else {
    assert(cmd.find(std::string{"sys_argv"}) != std::string::npos);
  }
  if (static_cast<int>(a.size()) > 1) {
    std::cout << a[1];
    std::cout << std::endl;
  } else {
    std::cout << std::string{"OK"};
    std::cout << std::endl;
  }
}
