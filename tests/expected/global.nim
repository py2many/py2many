import strutils
let code_0 = 0
let code_1 = 1
let l_a = @[code_0, code_1]
let code_a = "a"
let code_b = "b"
let l_b = @[code_a, code_b]
proc main() =
  for i in l_a:
    echo i
  for j in l_b:
    echo j
  if "a" in @["a", "b"]:
    echo "OK"


main()
