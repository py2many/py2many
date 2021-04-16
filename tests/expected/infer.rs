fn foo() {
    let a: i32 = 10;
    let b: i32 = a;
    assert!(b == 10);
    println!("{}", b);
}

fn main() {
    foo();
}
