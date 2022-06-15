type
  Foo = object

proc bar(self: Foo): string =
  return "a"


proc main() =
  let f = Foo()
  let b = f.bar()
  echo b

main()
