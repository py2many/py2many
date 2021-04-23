// @dart=2.9
import 'package:sprintf/sprintf.dart';

class Rectangle {
  int height;
  int length;

  Rectangle(this.height, this.length) {}
  bool is_square() {
    return height == length;
  }
}

show() {
  var r = Rectangle(1, 1);
  assert(r.is_square());
  r = Rectangle(1, 2);
  assert(!(r.is_square()));
  var h = r.height;
  var l = r.length;
  print(sprintf("%s", [h]));
  print(sprintf("%s", [l]));
}

void main() {
  show();
}
