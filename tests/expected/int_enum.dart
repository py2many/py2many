// @dart=2.9
import 'package:sprintf/sprintf.dart';

class Colors {
  ST0 RED;
  ST1 GREEN;
  ST2 BLUE;

  final RED = auto();
  final GREEN = auto();
  final BLUE = auto();
}

class Permissions {
  ST0 R;
  ST1 W;
  ST2 X;

  final int R = 1;
  final int W = 2;
  final int X = 16;
}

show() {
  final color_map = {
    Colors.RED: "red",
    Colors.GREEN: "green",
    Colors.BLUE: "blue"
  };
  final a = Colors.GREEN;

  if (a == Colors.GREEN) {
    print(sprintf("%s", ["green"]));
  } else {
    print(sprintf("%s", ["Not green"]));
  }
  final b = Permissions.R;

  if (b == Permissions.R) {
    print(sprintf("%s", ["R"]));
  } else {
    print(sprintf("%s", ["Not R"]));
  }
  assert(color_map.length != 0);
}

main() {
  show();
}
