// generated by py2many --d=1
import std;

bool nested_containers() {
  const int[][string] CODES = ["KEY" : [1, 3]];
  return CODES["KEY"].canFind(1);
}

void main(string[] argv) {

  if (nested_containers()) {
    writeln(format("%s", "OK"));
  }
}
