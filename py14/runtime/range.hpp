/* range.hpp
 #
 # Copyright (c) 2013 Alexander Duchene <aduche4@tigers.lsu.edu>
 #
 # This piece of software was created as part of the Drosophila  Population
 # Genomics Project opensource agreement.
 #
 # Permission is hereby granted, free of charge, to any person obtaining a copy
 # of this software and associated documentation files (the "Software"), to deal
 # in the Software without restriction, including without limitation the rights
 # to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 # copies of the Software, and to permit persons to whom the Software is
 # furnished to do so, subject to the following conditions:
 #
 # The above copyright notice and this permission notice shall be included in
 all
 # copies or substantial portions of the Software.
 #
 # THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 # IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 # FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 # AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 # LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 # OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 # SOFTWARE.
 */
#pragma once
#include <iterator>

namespace rangepp {

template <typename value_t>
class range_impl {
   private:
    value_t rbegin;
    value_t rend;
    value_t step;
    int step_end;

   public:
    range_impl(value_t begin, value_t end, value_t step = 1)
        : rbegin(begin), rend(end), step(step) {
        step_end = (rend - rbegin) / step;
        if (rbegin + step_end * step != rend) {
            step_end++;
        }
    }

    class iterator
        : public std::iterator<std::random_access_iterator_tag, value_t> {
       private:
        value_t current_value;
        int current_step;
        range_impl& parent;

       public:
        iterator(int start, range_impl& parent)
            : current_step(start), parent(parent) {
            current_value = parent.rbegin + current_step * parent.step;
        }
        value_t operator*() { return current_value; }
        const iterator* operator++() {
            current_value += parent.step;
            current_step++;
            return this;
        }
        const iterator* operator++(int) {
            current_value += parent.step;
            current_step++;
            return this;
        }
        bool operator==(const iterator& other) {
            return current_step == other.current_step;
        }
        bool operator!=(const iterator& other) {
            return current_step != other.current_step;
        }
        iterator operator+(int s) {
            iterator ret = *this;
            ret.current_step += s;
            ret.current_value += s * parent.step;
            return ret;
        }
        iterator operator-(int s) {
            iterator ret = *this;
            ret.current_step -= s;
            ret.current_value -= s * parent.step;
            return ret;
        }
        const iterator* operator--() {
            current_value -= parent.step;
            current_step--;
            return this;
        }
        iterator operator--(int) {
            iterator old = *this;
            current_value -= parent.step;
            current_step--;
            return old;
        }
    };

    iterator begin() { return iterator(0, *this); }
    iterator end() { return iterator(step_end, *this); }

    value_t operator[](int s) { return rbegin + s * step; }

    int size() { return step_end; }
};

auto xrange(int begin, int end, int stepsize) {
    return range_impl<int>(begin, end, stepsize);
}

auto xrange(int begin, int end) { return range_impl<int>(begin, end, 1); }

auto xrange(int end) { return range_impl<int>(0, end, 1); }

auto range(int begin, int end, int stepsize) {
    std::vector<int> r {};
    for(auto v : xrange(begin, end, stepsize)) {
        r.push_back(v);
    }
    return r; 
}

auto range(int begin, int end) {
    std::vector<int> r {};
    for(auto v : xrange(begin, end)) {
        r.push_back(v);
    }
    return r; 
}

auto range(int end) {
    std::vector<int> r {};
    for(auto v : xrange(end)) {
        r.push_back(v);
    }
    return r; 
}
}
