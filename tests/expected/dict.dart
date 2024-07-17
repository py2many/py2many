// @dart=3.4
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

int return_dict_index_str(String key) {
  final Map<String, int> CODES = {"KEY": 1};
  return (CODES[key] ?? (throw Exception("key not found")));
}

String return_dict_index_int(int key) {
  final Map<int, String> CODES = {1: "one"};
  return (CODES[key] ?? (throw Exception("key not found")));
}

main(List<String> argv) {
  assert(implicit_keys());
  assert(explicit_keys());
  assert(dict_values());
  assert(return_dict_index_str("KEY") == 1);
  assert(return_dict_index_int(1) == "one");
  print(sprintf("%s", ["OK"]));
}
