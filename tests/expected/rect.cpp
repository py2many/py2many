
class Rectangle {
  auto height = None;
  auto length = None;
  template <typename T1> auto is_square(T1 self) {
    return self.height == self.length;
  }
}
}
