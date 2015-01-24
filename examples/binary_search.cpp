#include "sys.h"
#include "builtins.h"
#include <iostream>
#include <string>
#include <vector>
#include <utility>
auto search = [](auto seq, auto key) {
    auto lo = 0;
    auto hi = py14::len(seq) - 1;
    while (hi >= lo) {
        auto mid = lo + hi - lo / 2;
        if (seq[mid] < key) {
            lo = mid + 1;
        } else {
            if (seq[mid] > key) {
                hi = mid - 1;
            } else {
                return mid;
            }
        }
        return false;
    }
};
int main(int argc, char** argv) {
    py14::sys::argv = std::vector<std::string>(argv, argv + argc);
    std::vector<decltype(1)> seq{1, 2, 5, 10, 11, 11, 12, 13, 17, 23};
    auto elem = search(seq, 12);
    if (elem) {
        std::cout << elem << std::endl;
    }
}
