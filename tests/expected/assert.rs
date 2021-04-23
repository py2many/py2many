fn compare_assert(a: i32, b: i32) {
    assert!(a == b);
    assert!(!(0 == 1));
}

fn main() {
    compare_assert(1, 1);
}
