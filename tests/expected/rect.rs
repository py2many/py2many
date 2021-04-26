struct Rectangle {
    height: i32,
    length: i32,
}

impl Rectangle {
    fn is_square(&self) -> bool {
        return self.height == self.length;
    }
}
fn show() {
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

fn main() {
    show();
}
