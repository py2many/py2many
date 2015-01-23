#include <iostream>
#include <string>
#include <vector>
#include <utility>
#include "sys.h"
auto map = [](auto values, auto fun) {
    std::vector<decltype(
        fun(std::declval<typename decltype(values)::value_type>()))> results{};
    for (auto v : values) {
        results.push_back(fun(v));
    }
    return results;
};
auto square = [](auto n) { return n * n; };
int main(int argc, char** argv) {
    py14::sys::argv = std::vector<std::string>(argv, argv + argc);
    std::vector<decltype(1)> values{1, 2, 3, 4, 5};
    auto results = map(values, square);
    for (auto v : results) {
        std::cout << v << std::endl;
    }
}
