const code_0: i32 = 0;
const code_1: i32 = 1;
const l_a: [i32; 2] = [code_0, code_1];
const code_a: &str = "a";
const code_b: &str = "b";
const l_b: [&str; 2] = [code_a, code_b];
fn main() {
    for i in l_a.iter() {
        println!("{}", i);
    }
    for i in l_b.iter() {
        println!("{}", i);
    }
}
