
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//!
//! ```

#![allow(clippy::upper_case_acronyms)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

pub fn test_python(iterations: i32) {
    let mut iteration: i32 = 0;
    let mut total: f64 = f64::from(0.0);
    let array_length: i32 = 1000;
    let array: Vec<i32> = (0..array_length).map(|i| i).collect::<Vec<_>>();
    println!("{} {}", "iterations", iterations);
    while iteration < iterations {
        let mut innerloop: i32 = 0;
        while innerloop < 100 {
            total += array[((iteration + innerloop) % array_length) as usize] as f64;
            innerloop += 1;
        }
        iteration += 1;
    }
    if total == 15150 as f64 {
        println!("{}", "OK");
    }
    drop(array);
}

pub fn main() {
    test_python(3);
}
