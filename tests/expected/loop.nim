proc for_with_break() =
  for i in (0..4 - 1):
    if i == 2:
      break;

    echo i

proc for_with_continue() =
  for i in (0..4 - 1):
    if i == 2:
      continue;

    echo i

proc for_with_else() =
  let has_break = false
  for i in (0..4 - 1):
    echo i
  if has_break != true:
    echo "OK"


proc while_with_break() =
  var i = 0
  while true:
    if i == 2:
      break;

    echo i
    i += 1;

proc while_with_continue() =
  var i = 0
  while i < 5:
    i += 1;
    if i == 2:
      continue;

    echo i

proc main() =
  for_with_break()
  for_with_continue()
  for_with_else()
  while_with_break()
  while_with_continue()

main()
