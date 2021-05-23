import sets
import strutils
import tables
let code_0 = 0
let code_1 = 1
let code_a = "a"
let code_b = "b"
let l_b = toHashSet([code_a])
let l_c = {code_b: code_0}.newTable
proc main() =
  assert("a" in l_b)
  echo "OK"

main()
