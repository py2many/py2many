import tables
proc nested_containers(): bool =
  let CODES = {"KEY": @[1, 3]}.newTable
  return 1 in CODES["KEY"]

proc main() =
  if nested_containers():
    echo "OK"


main()
