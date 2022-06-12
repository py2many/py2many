
proc main_func() =
  let a = int16(1)
  let b = a
  echo b
  let c = int64(1)
  let d = c
  echo d
  let e = uint64(1)
  let f = e
  echo f

proc main() =
  main_func()

main()
