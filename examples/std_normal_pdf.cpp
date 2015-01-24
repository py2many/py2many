#include "sys.h"
#include "builtins.h"
#include <iostream>
#include <string>
#include <cmath>
#include <vector>
#include <utility>
using namespace std::literals::string_literals;
auto pdf = [](auto x, auto mean, auto std_dev) {
    auto term1 = 1.0 / std::pow(2 * py14::math::pi, 0.5);
    auto term2 = std::pow(py14::math::e, -1.0 * std::pow(x - mean, 2.0) / 2.0 *
                                             std::pow(std_dev, 2.0));
    return term1 * term2;
};
int main(int argc, char** argv) {
    py14::sys::argv = std::vector<std::string>(argv, argv + argc);
    auto a = pdf(1, 0, 1);
    std::cout << std::to_string(a) + " should be close to "s +
                     std::to_string(0.241970724519) << std::endl;
}
