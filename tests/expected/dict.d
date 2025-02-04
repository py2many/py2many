// generated by py2many --dlang=1
import std;
import std.algorithm;

bool implicit_keys() {
  int[string] CODES = ["KEY": 1];
  return CODES.keys.canFind("KEY");
}

bool explicit_keys() {
  int[string] CODES = ["KEY": 1];
  return CODES.keys.canFind("KEY");
}

bool dict_values() {
  int[string] CODES = ["KEY": 1];
  return CODES.values.canFind(1);
}

int return_dict_index_str(string key) {
  int[string] CODES = ["KEY": 1];
  return CODES[key];
}

string return_dict_index_int(int key) {
  string[int] CODES = [1: "one"];
  return CODES[key];
}

void main(string[] argv) {
  assert(implicit_keys());
  assert(explicit_keys());
  assert(dict_values());
  assert(return_dict_index_str("KEY") == 1);
  assert(return_dict_index_int(1) == "one");
  writeln(format("%s", "OK"));
}
