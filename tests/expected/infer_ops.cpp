
inline void foo() {
  int a = 10;
  int b = 20;
  int c1 = a + b;
  int c2 = a - b;
  int c3 = a * b;
  double c4 = a / b;
  int c5 = -(a);
  double d = 2.0;
  double e1 = a + d;
  double e2 = a - d;
  double e3 = a * d;
  double e4 = a / d;
  double f = -3.0;
  int g = -(a);
}

template <typename T1, typename T2> auto add1(T1 x, T2 y) { return x + y; }

template <typename T1, typename T2> auto add2(T1 x, T2 y) { return x + y; }

template <typename T1, typename T2> auto add3(T1 x, T2 y) { return x + y; }

template <typename T1, typename T2> auto add4(T1 x, T2 y) { return x + y; }

template <typename T1, typename T2> auto add5(T1 x, T2 y) { return x + y; }

template <typename T1, typename T2> auto add6(T1 x, T2 y) { return x + y; }

template <typename T1, typename T2> auto add7(T1 x, T2 y) { return x + y; }

template <typename T1, typename T2> auto add8(T1 x, T2 y) { return x + y; }

template <typename T1, typename T2> auto add9(T1 x, T2 y) { return x + y; }

template <typename T1, typename T2> auto sub(T1 x, T2 y) { return x - y; }

template <typename T1, typename T2> auto mul(T1 x, T2 y) { return x * y; }

template <typename T1, typename T2> auto fadd(T1 x, T2 y) { return x + y; }

inline void show() {
  auto rv = fadd(6, 6.0);
  REQUIRE(rv == 12);
  std::cout << rv << std::endl;
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  foo();
  show();
}
