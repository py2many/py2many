// generated by py2many --d=1
import std;

const int CODE_0 = 0;
const int CODE_1 = 1;
const int[] L_A = [CODE_0, CODE_1];
const string CODE_A = "a";
const string CODE_B = "b";
const string[] L_B = [CODE_A, CODE_B];
void main(string[] argv) {
  foreach (i; L_A) {
    writeln(format("%s", i));
  }
  foreach (j; L_B) {
    writeln(format("%s", j));
  }

  if (["a", "b"].canFind("a")) {
    writeln(format("%s", "OK"));
  }
}
