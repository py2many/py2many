#include "pycpp/runtime/builtins.h"
#include "pycpp/runtime/sys.h"
#include <cassert>
#include <iostream>
/* This file implements a rectangle class  */

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
  std::cout << r.height;
  std::cout << std::endl;
  std::cout << r.length;
  std::cout << std::endl;
}

int main(int argc, char **argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  show();
}
