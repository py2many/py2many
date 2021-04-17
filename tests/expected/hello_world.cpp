#include "py14/runtime/builtins.h"
#include "py14/runtime/sys.h"
#include <iostream>
int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::cout << std::string{"Hello world!"};
  std::cout << std::endl;
  std::cout << std::string{"Hello"};
  std::cout << " ";
  std::cout << std::string{"world!"};
  std::cout << std::endl;
}
