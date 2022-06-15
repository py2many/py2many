proc default_builtins() =
  let a = ""
  let b = false
  let c = 0
  assert(a == "")
  assert(b == false)
  assert(c == 0)

proc main() =
  let a = max(1, 2)
  echo a
  let b = min(1, 2)
  echo b

main()
