#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

pub fn compare_assert(a: i32, b: i32) {
    assert!(a == b);
    assert!(!(0 == 1));
}

pub fn main() {
    assert!(true);
    assert!(!(false));
    compare_assert(1, 1);
    assert!(true);
    assert!(true);
    println!("{}", "OK");
}
