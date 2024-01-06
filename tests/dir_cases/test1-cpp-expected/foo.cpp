#include <cassert>  // NOLINT(build/include_order)
#include <cstdint>  // NOLINT(build/include_order)

#include "bar.h"
#include "baz.h"
int main(int argc, char** argv) {
  int x = bar1();
  std::string y = baz1();
  assert(x == 0);
  assert(y == std::string{"foo"});
}
