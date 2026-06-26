// @dart=3.4
import 'package:sprintf/sprintf.dart';

int global_var = 10;
test_global() {
//global global_var
  global_var = 20;
  print(sprintf("%s", [global_var]));
}

show() {
  test_global();
}

main(List<String> argv) {
  show();
}
