# This file implements a rectangle class


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
  echo r.height
  echo r.length

proc main() =
  show()

main()
