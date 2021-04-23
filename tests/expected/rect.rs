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
    let mut r: _ = Rectangle(1, 1);
    assert!(r.is_square());
    r = Rectangle(1, 2);
    assert!(!(r.is_square()));
    let h: _ = r.height;
    let l: _ = r.length;
    println!("{}", h);
    println!("{}", l);
}

fn main() {
    show();
}
