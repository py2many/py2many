class Rectangle {
  int height;
  int length;

  Rectangle(this.height, this.length) {}
  bool is_square() {
    return height == length;
  }
}
