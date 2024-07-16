// @dart=3.4
import 'package:sprintf/sprintf.dart';

do_unsupported() {
  final int a = 1;
/* dict comprehension ((key + 1), (value + 1)) unimplemented on line 9:4 */;
  final bool b = (a != 0);
  print(sprintf("%s", [b ? ("True") : ("False")]));
}

main(List<String> argv) {
  do_unsupported();
}
