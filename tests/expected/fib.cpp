template <typename T1> auto fib(T1 i) {
  if (i == 0 || i == 1) {
    return 1;
  }
  return fib(i - 1) + fib(i - 2);
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  auto rv = fib(5);
  std::cout << rv << std::endl;
}
