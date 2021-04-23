#include "py14/runtime/builtins.h"
#include "py14/runtime/sys.h"
#include <cassert>
#include <iostream>

class Rectangle {
public:
  int height;
  int length;

  Rectangle(int height, int length) {
    this->height = height;
    this->length = length;
  }
  inline bool is_square() { return this->height == this->length; }
};

inline void show() {
  Rectangle r = Rectangle(1, 1);
  assert(r.is_square());
  r = Rectangle(1, 2);
  assert(!(r.is_square()));
  auto h = r.height;
  auto l = r.length;
  std::cout << h;
  std::cout << std::endl;
  std::cout << l;
  std::cout << std::endl;
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  show();
}
