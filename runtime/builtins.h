#pragma once
#include <vector>
#include <string>
#include <cmath>
#include <boost/range/irange.hpp>

namespace py14 {
template <typename T>
auto len(T container) {
    return container.size();
}
auto range(int stop) { return boost::irange(1, stop); }
auto range(int start, int stop, int step = 1) {
    return boost::irange(start, stop, step);
}
namespace math {
const double pi = std::atan(1) * 4;
const double e = std::exp(1.0);
}
}
