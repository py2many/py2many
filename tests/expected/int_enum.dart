// @dart=2.9
import 'package:sprintf/sprintf.dart';
import 'package:vnum/vnum.dart';

enum Colors {
  RED,
  GREEN,
  BLUE,
}

@VnumDefinition
class Permissions extends Vnum<int> {
  static final R = const Permissions.define(1);
  static final W = const Permissions.define(2);
  static final X = const Permissions.define(16);

  const Permissions.define(int fromValue) : super.define(fromValue);
  factory Permissions(int value) => Vnum.fromValue(value, Permissions);
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
