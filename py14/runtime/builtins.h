#pragma once
#include <vector>
#include <string>
#include <numeric>
#include <cstdlib>
#include <iterator>

namespace py14 {

template <typename T>
auto to_int(T val) {
    return static_cast<int>(val);
}

template <>
auto to_int(std::string val) {
    return std::stoi(val);
}
}
