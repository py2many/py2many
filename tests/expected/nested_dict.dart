// @dart=3.4
import 'package:sprintf/sprintf.dart';

bool nested_containers() {
  final Map<String, List<int>> CODES = {
    "KEY": [1, 3]
  };
  return (CODES["KEY"] ?? (throw Exception("key not found"))).contains(1);
}

main(List<String> argv) {
  if (nested_containers()) {
    print(sprintf("%s", ["OK"]));
  }
}
