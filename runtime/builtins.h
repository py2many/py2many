#pragma once
#include <vector>
#include <string>
#include <boost/range/irange.hpp>

namespace py14 {

template <typename T>
auto to_int(T val) {
    return static_cast<int>(val);
}

template <>
auto to_int(std::string val) {
    return std::stoi(val);
}

template <typename T>
auto len(T container) {
    return container.size();
}

auto range(int stop) { return boost::irange(1, stop); }

auto range(int start, int stop, int step = 1) {
    return boost::irange(start, stop, step);
}
}
