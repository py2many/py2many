#include <iostream>
#include <string>
#include <vector>
#include <utility>
#include "sys.h"
template <typename T1>
auto fib(T1 n) {
    if (n == 1) {
        return 1;
    } else {
        if (n == 0) {
            return 0;
        } else {
            return fib(n - 1) + fib(n - 2);
        }
    }
}
int main(int argc, char** argv) {
    py14::sys::argv = std::vector<std::string>(argv, argv + argc);
    auto n = std::stoi(py14::sys::argv[1]);
    std::cout << fib(n) << std::endl;
}
