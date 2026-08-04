#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
#include <map>       // NOLINT(build/include_order)
#include <string>    // NOLINT(build/include_order)
#include <vector>    // NOLINT(build/include_order)
inline void show() {
  std::vector<int> my_list = {1, 2, 3, 4, 5};
  my_list.erase(my_list.begin() + 2);
  std::cout << static_cast<int>(my_list.size());
  std::cout << std::endl;
  std::map<std::string, int> my_dict = std::map<std::string, int>{
      {std::string{"a"}, 1}, {std::string{"b"}, 2}, {std::string{"c"}, 3}};
  my_dict.erase(std::string{"b"});
  std::cout << static_cast<int>(my_dict.size());
  std::cout << std::endl;
}

int main(int argc, char** argv) { show(); }
