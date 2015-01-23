#include "sys.h"
#include "builtins.h"
#include <iostream>
#include <string>
#include <vector>
#include <utility>
auto sort = [](auto seq) {
    auto L = py14::len(seq);
    for (auto _ : py14::range(L)) {
        for (auto n : py14::range(1, L)) {
            if (seq[n] < seq[n - 1]) {
                auto temp = seq[n - 1];
                seq[n - 1] = seq[n];
                seq[n] = temp;
            }
        }
    }
    return seq;
};
int main(int argc, char** argv) {
    py14::sys::argv = std::vector<std::string>(argv, argv + argc);
    std::vector<decltype(10)> unsorted{10, 6, 1, 0, 2, 3, 5, 1, 6, 2};
    auto sorted = sort(unsorted);
    for (auto n : sorted) {
        std::cout << n << std::endl;
    }
}
