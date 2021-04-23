#include "py14/runtime/builtins.h"
#include "py14/runtime/sys.h"
#include <iostream>

class Colors {
public:
  ST0 RED;
  ST1 GREEN;
  ST2 BLUE;

  auto RED = auto();
  auto GREEN = auto();
  auto BLUE = auto();
};

class Permissions {
public:
  ST0 R;
  ST1 W;
  ST2 X;

  int R = 1;
  int W = 2;
  int X = 16;
};

inline void show() {
  auto color_map = None;
  auto a = Colors.GREEN;
  if (a == Colors.GREEN) {
    std::cout << std::string{"green"};
    std::cout << std::endl;
  } else {
    std::cout << std::string{"Not green"};
    std::cout << std::endl;
  }
  auto b = Permissions.R;
  if (b == Permissions.R) {
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
