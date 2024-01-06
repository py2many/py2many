#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
#include <map>       // NOLINT(build/include_order)
#include <string>    // NOLINT(build/include_order)

class Colors : public std::string {
 public:
  Colors(const char* s) : std::string(s) {}  // NOLINT(runtime/explicit)
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
  std::cout << static_cast<int>(color_map.size());
  std::cout << std::endl;
}

int main(int argc, char** argv) { show(); }
