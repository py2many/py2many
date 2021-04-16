
class Rectangle {
  int height = None;
  int length = None;
  template <typename T1> auto is_square(T1 self) {
    return self.height == self.length;
  }

}

inline void
show() {
  auto r = Rectangle();
  REQUIRE(r.is_square());
  r = Rectangle();
  REQUIRE(!r.is_square());
  auto h = r.height;
  auto l = r.length;
  std::cout << h << std::endl;
  std::cout << l << std::endl;
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  show();
}
