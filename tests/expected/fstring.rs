
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//!
//! ```

#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

use std::collections;

pub fn main() {
    let a: i32 = 10;
    println!(
        "{}",
        vec!["hello ", &(a + 1).to_string(), " world"].join("")
    );
}
