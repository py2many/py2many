fn foo() {
    let a: i32 = 10;
    let b: i32 = 20;
    let _c1: i32 = (a + b);
    let _c2: i32 = (a - b);
    let _c3: i32 = (a * b);
    let _c4: f32 = (a / b) as f32;
    let _c5: i32 = -(a);
    let d: f32 = 2.0;
    let _e1: f32 = (a as f32 + d);
    let _e2: f32 = (a as f32 - d);
    let _e3: f32 = (a as f32 * d);
    let _e4: f32 = (a as f32 / d);
    let _f: f32 = -3.0;
    let _g: i32 = -(a);
}

fn add1(x: i8, y: i8) -> i16 {
    return (x + y) as i16;
}

fn add2(x: i16, y: i16) -> i32 {
    return (x + y) as i32;
}

fn add3(x: i32, y: i32) -> i64 {
    return (x + y) as i64;
}

fn add4(x: i64, y: i64) -> i64 {
    return (x + y);
}

fn add5(x: u8, y: u8) -> u16 {
    return (x + y) as u16;
}

fn add6(x: u16, y: u16) -> u32 {
    return (x + y) as u32;
}

fn add7(x: u32, y: u32) -> u64 {
    return (x + y) as u64;
}

fn add8(x: u64, y: u64) -> u64 {
    return (x + y);
}

fn add9(x: i8, y: u16) -> u32 {
    return (x as u16 + y) as u32;
}

fn sub(x: i8, y: i8) -> i8 {
    return (x - y);
}

fn mul(x: i8, y: i8) -> i16 {
    return (x * y) as i16;
}

fn fadd1(x: i8, y: f32) -> f32 {
    return (x as f32 + y);
}

fn show() {
    let rv: f32 = fadd1(6, 6.0);
    assert!(rv == 12 as f32);
    println!("{}", "OK");
}

fn main() {
    foo();
    show();
}
