use std::collections;
pub const code_0: i32 = 0;
pub const code_1: i32 = 1;
pub const l_a: &[i32; 2] = &[code_0, code_1];
pub const code_a: &str = "a";
pub const code_b: &str = "b";
pub const l_b: &[&str; 2] = &[code_a, code_b];
pub fn main() {
    for i in l_a {
        println!("{}", *i);
    }
    for i in l_b {
        println!("{}", *i);
    }
    if vec!["a", "b"].iter().any(|&x| x == "a") {
        println!("{}", "OK");
    }
}
