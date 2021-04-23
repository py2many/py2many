fn foo() {
    let a: i32 = 10;
    let b: i32 = 20;
    let c1: i32 = (a + b);
    let c2: i32 = (a - b);
    let c3: i32 = (a * b);
    let c4: f32 = (a / b);
    let c5: i32 = -(a);
    let d: f32 = 2.0;
    let e1: f32 = (a + d);
    let e2: f32 = (a - d);
    let e3: f32 = (a * d);
    let e4: f32 = (a / d);
    let f: f32 = -3.0;
    let g: i32 = -(a);
}

fn add1(x: i8, y: i8) -> i16 {
    return (x + y);
}

fn add2(x: i16, y: i16) -> i32 {
    return (x + y);
}

fn add3(x: i32, y: i32) -> i64 {
    return (x + y);
}

fn add4(x: i64, y: i64) -> i64 {
    return (x + y);
}

fn add5(x: u8, y: u8) -> u16 {
    return (x + y);
}

fn add6(x: u16, y: u16) -> u32 {
    return (x + y);
}

fn add7(x: u32, y: u32) -> u64 {
    return (x + y);
}

fn add8(x: u64, y: u64) -> u64 {
    return (x + y);
}

fn add9(x: i8, y: u16) -> u32 {
    return (x + y);
}

fn sub(x: i8, y: i8) -> i8 {
    return (x - y);
}

fn mul(x: i8, y: i8) -> i16 {
    return (x * y);
}

fn fadd1(x: i8, y: f32) -> f32 {
    return (x + y);
}

fn show() {
    let rv: f32 = fadd1(6, 6.0);
    assert!(rv == 12);
    println!("{}", "OK");
}

fn main() {
    foo();
    show();
}
