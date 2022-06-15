import os
import strutils


proc main() =
  let a: seq[string] = (@[getAppFilename()] & commandLineParams())
  let cmd: string = a[0]
  if cmd == "dart":
    discard
  else:
    assert("sys_argv" in cmd)
  if len(a) > 1:
    echo a[1]
  else:
    echo "OK"

main()
