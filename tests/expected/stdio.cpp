#include <cstdint>   // NOLINT(build/include_order)
#include <iostream>  // NOLINT(build/include_order)

inline void main_func() { std::cout << std::string{"foobar\n"}; }

int main(int argc, char** argv) { main_func(); }
