#include <cassert>   // NOLINT(build/include_order)
#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)

inline void foo() {
  int a = 10;
  int b = 20;
  int _c1 = a + b;
  int _c2 = a - b;
  int _c3 = a * b;
  double _c4 = a / b;
  int _c5 = -(a);
  double d = 2.0;
  double _e1 = a + d;
  double _e2 = a - d;
  double _e3 = a * d;
  double _e4 = a / d;
  double _f = -3.0;
  int _g = -(a);
}

inline int16_t add1(int8_t x, int8_t y) { return x + y; }

inline int32_t add2(int16_t x, int16_t y) { return x + y; }

inline int64_t add3(int32_t x, int32_t y) { return x + y; }

inline int64_t add4(int64_t x, int64_t y) { return x + y; }

inline uint16_t add5(uint8_t x, uint8_t y) { return x + y; }

inline uint32_t add6(uint16_t x, uint16_t y) { return x + y; }

inline uint64_t add7(uint32_t x, uint32_t y) { return x + y; }

inline uint64_t add8(uint64_t x, uint64_t y) { return x + y; }

inline uint32_t add9(int8_t x, uint16_t y) { return x + y; }

inline int8_t sub(int8_t x, int8_t y) { return x - y; }

inline int16_t mul(int8_t x, int8_t y) { return x * y; }

inline double fadd1(int8_t x, double y) { return x + y; }

inline void show() {
  assert(fadd1(6, 6.0) == 12);
  std::cout << std::string{"OK"};
  std::cout << std::endl;
}

int main(int argc, char** argv) {
  foo();
  show();
}
