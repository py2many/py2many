
proc main_func() =
  var ands: seq[bool] = @[]
  var ors: seq[bool] = @[]
  var xors: seq[bool] = @[]
  for a in @[false, true]:
    for b in @[false, true]:
      ands.add((a and b))
      ors.add((a or b))
      xors.add((a xor b))
  assert(ands == @[false, false, false, true])
  assert(ors == @[false, true, true, true])
  assert(xors == @[false, true, true, false])
  echo "OK"

proc main() =
  main_func()

main()
