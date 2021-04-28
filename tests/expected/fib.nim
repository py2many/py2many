proc fib(i: int): int =
  if i == 0 or i == 1:
    return 1

  return (fib((i - 1)) + fib((i - 2)))

proc main() =
  let rv = fib(5)
  echo rv

main()
