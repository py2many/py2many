
class Colors {
  auto RED = auto();
  auto GREEN = auto();
  auto BLUE = auto();
}

class Permissions {
  int R = 1;
  int W = 2;
  int X = 16;
}

inline void
show() {
  auto color_map = None;
  auto a = Colors.GREEN;
  if (a == Colors.GREEN) {
    std::cout << std::string{"green"} << std::endl;
  } else {
    std::cout << std::string{"Not green"} << std::endl;
  }
  auto b = Permissions.R;
  if (b == Permissions.R) {
    std::cout << std::string{"R"} << std::endl;
  } else {
    std::cout << std::string{"Not R"} << std::endl;
  }
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  show();
}
