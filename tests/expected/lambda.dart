// @dart=2.9
import 'package:sprintf/sprintf.dart';

 show() {
Callable myfunc = { x, y -> (x + y) };
print(sprintf("%s", [myfunc(1, 2)]));}


void main() {
show();
}

