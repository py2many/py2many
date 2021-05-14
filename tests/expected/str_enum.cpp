#include "pycpp/runtime/builtins.h"
#include "pycpp/runtime/sys.h"
#include <iostream>
#include <map>

class Colors : public std::string {
public:
  Colors(const char *s) : std::string(s) {}
  static const Colors RED;
  static const Colors GREEN;
  static const Colors BLUE;
};

const Colors Colors::RED = "red";
const Colors Colors::GREEN = "green";
const Colors Colors::BLUE = "blue";

inline void show() {
  std::map<Colors, std::string> color_map =
      std::map<Colors, std::string>{{Colors::RED, std::string{"1"}},
                                    {Colors::GREEN, std::string{"2"}},
                                    {Colors::BLUE, std::string{"3"}}};
  Colors a = Colors::GREEN;
  if (a == Colors::GREEN) {
    std::cout << std::string{"green"};
    std::cout << std::endl;
  } else {
    std::cout << std::string{"Not green"};
    std::cout << std::endl;
  }
  std::cout << color_map.size();
  std::cout << std::endl;
}

int main(int argc, char **argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  show();
}
