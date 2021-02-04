inline void foo() {
  int a = 10;
  int b = a;
}
int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  foo();
}
