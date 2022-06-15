proc do_unsupported() =
  let a = 1
  # dict comprehension ((key + 1), (value + 1)) unimplemented on line 9:4
  let b = bool(a)
  echo if b: "True" else: "False"

proc main() =
  do_unsupported()

main()
