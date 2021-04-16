inline void show() {
  std::cout << 2 << std::endl;
  std::cout << std::string{"b"} << std::endl;
  std::cout << 2 << std::endl;
  std::cout << std::string{"b"} << std::endl;
}

int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  show();
}
