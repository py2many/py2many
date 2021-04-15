int main(int argc, char **argv) {
  py14::sys::argv = std::vector<std::string>(argv, argv + argc);
  std::cout << std::string{"Hello world!"} << std::endl;
  std::cout << std::string{"Hello"} << std::endl;
  std::cout << std::string{"world!"} << std::endl;
}
