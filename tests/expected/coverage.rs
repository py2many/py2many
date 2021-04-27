use std::collections;

fn indexing() -> i32 {
    let mut sum: i32 = 0;
    let mut a: Vec<i32> = vec![];
    for i in (0..10) {
        a.push(i);
        sum += a[i as usize];
    }
    return sum;
}

fn show() {
    let a1: i32 = 10;
    let a2: f32 = 2.1;
    println!("{}", a2);
    for i in (0..10) {
        println!("{}", i);
    }
    for i in (0..10).step_by(2) {
        println!("{}", i);
    }
    let a3: i32 = -(a1);
    let a4: i32 = (a3 + a1);
    println!("{}", a4);
    let sum1: i32 = indexing();
    println!("{}", sum1);
    let a5: &Vec<i32> = &vec![1, 2, 3];
    println!("{}", a5.len());
    let a9: Vec<&str> = vec!["a", "b", "c", "d"];
    println!("{}", a9.len());
    if Some(1) != None {
        println!("{}", "World is sane");
    }
}

fn main() {
    show();
}
