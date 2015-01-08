#include <string>
#include <vector>
#include <iostream>
#include <boost/python.hpp>
#include <boost/python/list.hpp>
#include <boost/python/stl_iterator.hpp>

namespace py = boost::python;

template <typename T1, typename T2>
auto adder(T1 a, T2 b) {
    return a + b;
}

template <typename T1>
auto lister(T1 l) {
    for (auto const e : l) {
        std::cout << e << std::endl;
    }
    return l;
}

template <typename T>
std::vector<T> to_vector(py::list list) {
    py::stl_input_iterator<T> begin(list), end{};
    return std::vector<T>(begin, end);
}

template <typename T>
py::list to_list(std::vector<T> vector) {
    py::list list{};
    for (auto const e : vector) {
        list.append(py::object(e));
    }
    return list;
}

template <typename T>
auto lister_converter(py::list list) {
    return to_list<T>(lister(to_vector<T>(list)));
}

BOOST_PYTHON_MODULE(extern_functions) {
    using namespace boost::python;

    def("adder", adder<std::string, std::string>);
    def("lister", lister_converter<std::string>);
}
