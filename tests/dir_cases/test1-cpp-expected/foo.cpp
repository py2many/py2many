#include <cassert>  // NOLINT(build/include_order)

#include "bar.h"
#include "baz.h"
#include "pycpp/runtime/builtins.h"  // NOLINT(build/include_order)
#include "pycpp/runtime/sys.h"       // NOLINT(build/include_order)
int main(int argc, char** argv) {
  pycpp::sys::argv = std::vector<std::string>(argv, argv + argc);
  int x = bar1();
  std::string y = baz1();
  assert(x == 0);
  assert(y == std::string{"foo"});
}
