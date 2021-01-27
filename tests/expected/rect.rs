struct Rectangle {
    height: i32,
    length: i32,
}

impl Rectangle {
    fn is_square(&self) -> bool {
        return self.height == self.length;
    }
}
