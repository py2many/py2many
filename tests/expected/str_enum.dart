// @dart=2.9
import 'package:sprintf/sprintf.dart';
import 'package:vnum/vnum.dart';

@VnumDefinition
class Colors extends Vnum<String> {
  static final RED = const Colors.define("red");
  static final GREEN = const Colors.define("green");
  static final BLUE = const Colors.define("blue");

  const Colors.define(String fromValue) : super.define(fromValue);
  factory Colors(String value) => Vnum.fromValue(value, Colors);
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
