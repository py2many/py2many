
template <typename T1, typename T2> auto bisect_right(T1 data, T2 item) {
  int low = 0;
  auto high = data.size();
  while (low < high) {
    auto middle = py14::to_int(low + high / 2);
    if (item < data[middle]) {
      high = middle;
    } else {
      low = middle + 1;
    }
  }
  return low;
}

template <typename T1, typename T2> auto bin_it(T1 limits, T2 data) {
  std::vector<decltype(0)> bins{0};
  for (auto x : limits) {
    bins.push_back(0);
  }
  for (auto d : data) {
    bins[bisect_right(limits, d)] += 1;
  }
  return bins;
}
