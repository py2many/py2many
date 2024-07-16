// @dart=3.4
import 'package:sprintf/sprintf.dart';
/* This file implements a rectangle class  */

class Rectangle {
  int height;
  int length;

  Rectangle(this.height, this.length) {}
  bool is_square() {
    return height == length;
  }
}

show() {
  Rectangle r = Rectangle(1, 1);
  assert(r.is_square());
  r = Rectangle(1, 2);
  assert(!(r.is_square()));
  print(sprintf("%s", [r.height]));
  print(sprintf("%s", [r.length]));
}

main(List<String> argv) {
  show();
}
