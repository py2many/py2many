// @dart=2.9
import 'package:sprintf/sprintf.dart';

main(List<String> argv) {
  List<String> a = (new List<String>.from([''])..addAll(argv));
  String cmd = a[0];
  assert(cmd.contains("sys_argv"));

  if (a.length > 1) {
    print(sprintf("%s", [a[1]]));
  } else {
    print(sprintf("%s", ["OK"]));
  }
}
