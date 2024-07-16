// @dart=3.4
import 'package:sprintf/sprintf.dart';

inline_pass() {
  /* pass */
}

inline_ellipsis() {
  /* ... */
}

int indexing() {
  int sum = 0;
  List<int> a = [];
  for (final i in ([for (var i = 0; i < 10; i += 1) i])) {
    a.add(i);
    sum += (a[i] ?? (throw Exception("key not found")));
  }
  return sum;
}

bool infer_bool(int code) {
  return [1, 2, 4].contains(code);
}

show() {
  int a1 = 10;
  final int b1 = 15;
  final int b2 = 15;
  assert(b1 == 15);
  assert(b2 == 15);
  final int b9 = 2;
  final int b10 = 2;
  assert(b9 == b10);
  double a2 = 2.1;
  print(sprintf("%s", [a2]));
  for (final i in ([for (var i = 0; i < 10; i += 1) i])) {
    print(sprintf("%s", [i]));
  }
  for (final i in ([for (var i = 0; i < 10; i += 2) i])) {
    print(sprintf("%s", [i]));
  }
  final int a3 = -(a1);
  final int a4 = (a3 + a1);
  print(sprintf("%s", [a4]));
  final t1 = a1 > 5 ? (10) : (5);
  assert(t1 == 10);
  final int sum1 = indexing();
  print(sprintf("%s", [sum1]));
  final List<int> a5 = [1, 2, 3];
  print(sprintf("%s", [a5.length]));
  List<String> a9 = ["a", "b", "c", "d"];
  print(sprintf("%s", [a9.length]));
  final Map<String, int> a7 = {"a": 1, "b": 2};
  print(sprintf("%s", [a7.length]));
  final bool a8 = true;

  if (a8) {
    print(sprintf("%s", ["true"]));
  } else {
    if (a4 > 0) {
      print(sprintf("%s", ["never get here"]));
    }
  }

  if (a1 == 11) {
    print(sprintf("%s", ["false"]));
  } else {
    print(sprintf("%s", ["true"]));
  }

  if (1 != null) {
    print(sprintf("%s", ["World is sane"]));
  }
  print(sprintf("%s", [true ? ("True") : ("False")]));

  if (true) {
    a1 += 1;
  }
  assert(a1 == 11);

  if (true) {
    print(sprintf("%s", ["true"]));
  }
  inline_pass();
  final String s = "1    2";
  print(sprintf("%s", [s]));
  assert(infer_bool(1));
  final String _escape_quotes = " foo \"bar\" baz ";
  assert("aaabbccc".contains("bbc"));
  assert((1 != 0));
  final int _c1 = 1;
  2;
  final int _c2 = 3;
}

main(List<String> argv) {
  show();
}
