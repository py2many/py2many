pub struct Rectangle {
    pub height: i32,
    pub length: i32,
}

impl Rectangle {
    pub fn is_square(&self) -> bool {
        return self.height == self.length;
    }
}
pub fn show() {
    let mut r: Rectangle = Rectangle {
        height: 1,
        length: 1,
    };
    assert!(r.is_square());
    r = Rectangle {
        height: 1,
        length: 2,
    };
    assert!(!(r.is_square()));
    println!("{}", r.height);
    println!("{}", r.length);
}

pub fn main() {
    show();
}
