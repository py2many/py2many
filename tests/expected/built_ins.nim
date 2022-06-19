proc default_builtins() =
  let a = ""
  let b = false
  let c = 0
  let d = 0.0
  assert(a == "")
  assert(b == false)
  assert(c == 0)
  assert(d == 0.0)

proc main() =
  let a = max(1, 2)
  echo a
  let b = min(1, 2)
  echo b
  let c = int(min(1.0, 2.0))
  echo c

main()
