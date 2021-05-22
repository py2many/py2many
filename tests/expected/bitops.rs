
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

use std::collections;

pub fn main_func() {
    let mut ands: Vec<bool> = vec![];
    let mut ors: Vec<bool> = vec![];
    let mut xors: Vec<bool> = vec![];
    for a in vec![false, true] {
        for b in vec![false, true] {
            ands.push((a & b));
            ors.push((a | b));
            xors.push((a ^ b));
        }
    }
    assert!(ands == vec![false, false, false, true]);
    assert!(ors == vec![false, true, true, true]);
    assert!(xors == vec![false, true, true, false]);
    println!("{}", "OK");
}

pub fn main() {
    main_func();
}
