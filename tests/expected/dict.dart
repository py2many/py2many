// @dart=2.9
import 'package:sprintf/sprintf.dart';

bool implicit_keys() {
  final Map<String, int> CODES = {"KEY": 1};
  return CODES.keys.contains("KEY");
}

bool explicit_keys() {
  final Map<String, int> CODES = {"KEY": 1};
  return CODES.keys.contains("KEY");
}

bool dict_values() {
  final Map<String, int> CODES = {"KEY": 1};
  return CODES.values.contains(1);
}

main(List<String> argv) {
  assert(implicit_keys());
  assert(explicit_keys());
  assert(dict_values());
  print(sprintf("%s", ["OK"]));
}
