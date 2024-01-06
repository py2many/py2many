#include <algorithm>               // NOLINT(build/include_order)
#include <cassert>                 // NOLINT(build/include_order)
#include <cppitertools/range.hpp>  // NOLINT(build/include_order)
#include <cstdint>                 // NOLINT(build/include_order)
#include <iostream>                // NOLINT(build/include_order)
#include <map>                     // NOLINT(build/include_order)
#include <vector>                  // NOLINT(build/include_order)

inline void inline_pass() {
/* pass */}

inline void inline_ellipsis() {
/* ... */}

inline int indexing() {
  int sum = 0;
  std::vector<int> a = {};
  for (auto i : iter::range(10)) {
    a.push_back(i);
    sum += a[i];
  }
  return sum;
}

inline auto infer_bool(int code) {
  return ({
    std::vector<int> __tmp1 = {1, 2, 4};
    (std::find(__tmp1.begin(), __tmp1.end(), code) != __tmp1.end());
  });
}

inline void show() {
  int a1 = 10;
  int b1 = 15;
  int b2 = 15;
  assert(b1 == 15);
  assert(b2 == 15);
  int b9 = 2;
  int b10 = 2;
  assert(b9 == b10);
  double a2 = 2.1;
  std::cout << a2;
  std::cout << std::endl;
  for (auto i : iter::range(0, 10)) {
    std::cout << i;
    std::cout << std::endl;
  }
  for (auto i : iter::range(0, 10, 2)) {
    std::cout << i;
    std::cout << std::endl;
  }
  int a3 = -(a1);
  int a4 = a3 + a1;
  std::cout << a4;
  std::cout << std::endl;
  auto t1 = (a1 > 5 ? ({ 10; }) : ({ 5; }));
  assert(t1 == 10);
  int sum1 = indexing();
  std::cout << sum1;
  std::cout << std::endl;
  std::vector<int> a5 = {1, 2, 3};
  std::cout << static_cast<int>(a5.size());
  std::cout << std::endl;
  std::vector<std::string> a9 = {std::string{"a"}, std::string{"b"},
                                 std::string{"c"}, std::string{"d"}};
  std::cout << static_cast<int>(a9.size());
  std::cout << std::endl;
  std::map<std::string, int> a7 =
      std::map<std::string, int>{{std::string{"a"}, 1}, {std::string{"b"}, 2}};
  std::cout << static_cast<int>(a7.size());
  std::cout << std::endl;
  bool a8 = true;
  if (a8) {
    std::cout << std::string{"true"};
    std::cout << std::endl;
  } else {
    if (a4 > 0) {
      std::cout << std::string{"never get here"};
      std::cout << std::endl;
    }
  }
  if (a1 == 11) {
    std::cout << std::string{"false"};
    std::cout << std::endl;
  } else {
    std::cout << std::string{"true"};
    std::cout << std::endl;
  }
  if (1 != NULL) {
    std::cout << std::string{"World is sane"};
    std::cout << std::endl;
  }
  std::cout << (true ? ({ std::string{"True"}; })
                     : ({ std::string{"False"}; }));
  std::cout << std::endl;
  if (true) {
    a1 += 1;
  }
  assert(a1 == 11);
  if (true) {
    std::cout << std::string{"true"};
    std::cout << std::endl;
  }
  inline_pass();
  std::string s = std::string{"1    2"};
  std::cout << s;
  std::cout << std::endl;
  assert(infer_bool(1));
  std::string _escape_quotes = std::string{" foo \"bar\" baz "};
  assert(std::string{"aaabbccc"}.find(std::string{"bbc"}) != std::string::npos);
  assert(static_cast<bool>(1));
  int _c1 = 1;
  (void)2;
  int _c2 = 3;
}

int main(int argc, char** argv) { show(); }
