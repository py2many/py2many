// @dart=2.9
import 'dart:io';
import 'package:sprintf/sprintf.dart';

main(List<String> argv) {
  List<String> a = (new List<String>.from([Platform.executable])..addAll(argv));
  String cmd = a[0];

  if (cmd == "dart") {
/* pass */
  } else {
    assert(cmd.contains("sys_argv"));
  }

  if (a.length > 1) {
    print(sprintf("%s", [a[1]]));
  } else {
    print(sprintf("%s", ["OK"]));
  }
}
