
struct Rectangle {
height: int,
length: int,
}

impl Rectangle {
proc is_square(&self): bool =
    return self.height == self.length 
}
