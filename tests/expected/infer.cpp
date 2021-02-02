inline void foo() {
  auto a = 10;
  auto b = a;
}
int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  foo();
}
