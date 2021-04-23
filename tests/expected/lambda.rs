fn show() {
    let myfunc: _ = |x, y| (x + y);
    println!("{}", myfunc(1, 2));
}

fn main() {
    show();
}
