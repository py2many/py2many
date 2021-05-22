
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
    let myfunc: _ = |x, y| (x + y);
    println!("{}", myfunc(1, 2));
}

pub fn main() {
    show();
}
