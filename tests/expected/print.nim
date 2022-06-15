proc show() =
  echo "b"
  echo 2, " ", "b"
  let a: float64 = 2.1
  echo a
  let b = 2.1
  echo b
  let c = true
  echo if c: "True" else: "False"

proc main() =
  show()

main()
