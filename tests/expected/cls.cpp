#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
class Foo {
 public:
  inline std::string bar() { return std::string{"a"}; }
};

int main(int argc, char** argv) {
  Foo f = Foo();
  auto b = f.bar();
  std::cout << b;
  std::cout << std::endl;
}
