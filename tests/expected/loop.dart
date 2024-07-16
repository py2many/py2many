// @dart=3.4
import 'package:sprintf/sprintf.dart';

for_with_break() {
  for (final i in ([for (var i = 0; i < 4; i += 1) i])) {
    if (i == 2) {
      break;
    }
    print(sprintf("%s", [i]));
  }
}

for_with_continue() {
  for (final i in ([for (var i = 0; i < 4; i += 1) i])) {
    if (i == 2) {
      continue;
    }
    print(sprintf("%s", [i]));
  }
}

for_with_else() {
  final bool has_break = false;
  for (final i in ([for (var i = 0; i < 4; i += 1) i])) {
    print(sprintf("%s", [i]));
  }

  if (has_break != true) {
    print(sprintf("%s", ["OK"]));
  }
}

while_with_break() {
  int i = 0;
  while (true) {
    if (i == 2) {
      break;
    }
    print(sprintf("%s", [i]));
    i += 1;
  }
}

while_with_continue() {
  int i = 0;
  while (i < 5) {
    i += 1;

    if (i == 2) {
      continue;
    }
    print(sprintf("%s", [i]));
  }
}

main(List<String> argv) {
  for_with_break();
  for_with_continue();
  for_with_else();
  while_with_break();
  while_with_continue();
}
