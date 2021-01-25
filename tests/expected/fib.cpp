template <typename T1> auto fib(T1 i) {
  if (i == 0 || i == 1) {
    return 1;
  }
  return fib(i - 1) + fib(i - 2);
}
