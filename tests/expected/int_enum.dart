// @dart=3.4
import 'package:sprintf/sprintf.dart';

enum Colors {
  RED,
  GREEN,
  BLUE;
}

enum Permissions {
  R(1),
  W(2),
  X(16);

  const Permissions(this.__private);
  final int __private;
}

show() {
  final Map<Colors, String> color_map = {
    Colors.RED: "red",
    Colors.GREEN: "green",
    Colors.BLUE: "blue"
  };
  final Colors a = Colors.GREEN;

  if (a == Colors.GREEN) {
    print(sprintf("%s", ["green"]));
  } else {
    print(sprintf("%s", ["Not green"]));
  }
  final Permissions b = Permissions.R;

  if (b == Permissions.R) {
    print(sprintf("%s", ["R"]));
  } else {
    print(sprintf("%s", ["Not R"]));
  }
  assert(color_map.length != 0);
}

main(List<String> argv) {
  show();
}
