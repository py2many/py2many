#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)
inline void do_unsupported() {
  int a = 1;
  /* dict comprehension (key + 1, value + 1) unimplemented on line 9:4 */;
  bool b = static_cast<bool>(a);
  std::cout << (b ? ({ std::string{"True"}; }) : ({ std::string{"False"}; }));
  std::cout << std::endl;
}

int main(int argc, char** argv) { do_unsupported(); }
