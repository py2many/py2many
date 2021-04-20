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
}

fn main() {
    show();
}
