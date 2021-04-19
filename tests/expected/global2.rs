// cargo-deps: lazy_static
extern crate lazy_static;
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::collections::HashSet;
const code_0: i32 = 0;
const code_1: i32 = 1;
const code_a: &str = "a";
const code_b: &str = "b";
lazy_static! {
    static ref l_b: HashSet<&'static str> = [code_a].iter().cloned().collect::<HashSet<_>>();
}
lazy_static! {
    static ref l_c: HashMap<&'static str, i32> = [(code_b, code_0)]
        .iter()
        .cloned()
        .collect::<HashMap<_, _>>();
}
fn main() {
    assert!(l_b.iter().any(|&x| x == "a"));
    println!("{}", "OK");
}
