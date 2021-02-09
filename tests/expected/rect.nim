
type
    Rectangle = object
        height: int
        length: int
proc is_square(self: Rectangle): bool =
    return self.height == self.length


