#pragma once
#include <vector>
#include <string>
#include <numeric>

namespace py14 {

template <typename T>
auto to_int(T val) {
    return static_cast<int>(val);
}

template <>
auto to_int(std::string val) {
    return std::stoi(val);
}

auto range(int start, int stop, int step = 1) {
    //Completly wrong!! Just a temp hack
    std::vector<int> nums(stop - start);
    std::iota(nums.begin(), nums.end(), start);
    return nums;
}

auto range(int stop) { return range(1, stop); }
}
