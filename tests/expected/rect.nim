
type
  Rectangle = object
    height: int
    length: int
proc is_square(self: Rectangle): bool =
  return self.height == self.length


proc show() =
  var r = Rectangle(height: 1, length: 1)
  assert(r.is_square())
  r = Rectangle(height: 1, length: 2)
  assert(not (r.is_square()))
  let h = r.height
  let l = r.length
  echo h
  echo l

proc main() =
  show()

main()
