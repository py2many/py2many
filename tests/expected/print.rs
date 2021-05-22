
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//!
//! ```

#![allow(clippy::redundant_static_lifetimes)]
#![allow(clippy::upper_case_acronyms)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

pub fn show() {
    println!("{}", "b");
    println!("{} {}", 2, "b");
    let a: f64 = 2.1;
    println!("{}", a);
    let b: f64 = 2.1;
    println!("{}", b);
    let c: bool = true;
    println!("{}", if c { "True" } else { "False" });
}

pub fn main() {
    show();
}
