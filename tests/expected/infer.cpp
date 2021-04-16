inline void foo() {
  int a = 10;
  int b = a;
  REQUIRE(b == 10);
  std::cout << b << std::endl;
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  foo();
}
