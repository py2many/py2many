#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
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

int main(int argc, char** argv) { show(); }
