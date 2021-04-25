#include "py14/runtime/builtins.h"
#include "py14/runtime/sys.h"
#include <iostream>
#include <map>

enum Colors : int {
  RED = 0,
  GREEN = 1,
  BLUE = 2,
};

enum Permissions : int {
  R = 1,
  W = 2,
  X = 16,
};

inline void show() {
  auto color_map =
      std::map<int, std::string>{{Colors::RED, std::string{"red"}},
                                 {Colors::GREEN, std::string{"green"}},
                                 {Colors::BLUE, std::string{"blue"}}};
  auto a = Colors::GREEN;
  if (a == Colors::GREEN) {
    std::cout << std::string{"green"};
    std::cout << std::endl;
  } else {
    std::cout << std::string{"Not green"};
    std::cout << std::endl;
  }
  auto b = Permissions::R;
  if (b == Permissions::R) {
    std::cout << std::string{"R"};
    std::cout << std::endl;
  } else {
    std::cout << std::string{"Not R"};
    std::cout << std::endl;
  }
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  show();
}
