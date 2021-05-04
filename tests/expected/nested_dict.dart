// @dart=2.9
import 'package:sprintf/sprintf.dart';

bool nested_containers() {
  final Map<String, List<int>> CODES = {
    "KEY": [1, 3]
  };
  return CODES["KEY"].contains(1);
}

main() {
  if (nested_containers()) {
    print(sprintf("%s", ["OK"]));
  }
}
