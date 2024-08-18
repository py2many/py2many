// @dart=3.4
import 'package:sprintf/sprintf.dart';

enum Colors {
  RED("red"),
  GREEN("green"),
  BLUE("blue");

  const Colors(this.__private);
  final String __private;
}

show() {
  final Map<Colors, String> color_map = {
    Colors.RED: "1",
    Colors.GREEN: "2",
    Colors.BLUE: "3"
  };
  final Colors a = Colors.GREEN;

  if (a == Colors.GREEN) {
    print(sprintf("%s", ["green"]));
  } else {
    print(sprintf("%s", ["Not green"]));
  }
  print(sprintf("%s", [color_map.length]));
}

main(List<String> argv) {
  show();
}
