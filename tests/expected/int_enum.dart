// @dart=2.9
import 'package:sprintf/sprintf.dart';

class Colors {
  ST0 RED;
  ST1 GREEN;
  ST2 BLUE;

  var RED = auto();
  var GREEN = auto();
  var BLUE = auto();
}

class Permissions {
  ST0 R;
  ST1 W;
  ST2 X;

  int R = 1;
  int W = 2;
  int X = 16;
}

show() {
  var color_map = {
    Colors.RED: "red",
    Colors.GREEN: "green",
    Colors.BLUE: "blue"
  };
  var a = Colors.GREEN;

  if (a == Colors.GREEN) {
    print(sprintf("%s", ["green"]));
  } else {
    print(sprintf("%s", ["Not green"]));
  }
  var b = Permissions.R;

  if (b == Permissions.R) {
    print(sprintf("%s", ["R"]));
  } else {
    print(sprintf("%s", ["Not R"]));
  }
  assert(color_map.length != 0);
}

void main() {
  show();
}
