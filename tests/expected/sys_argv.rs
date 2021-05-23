
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

use std::env;

pub fn main() {
    let a: Vec<&str> = env::args()
        .map(|s| &*Box::leak(s.into_boxed_str()))
        .collect();
    let cmd: &str = a[0 as usize];
    assert!(cmd != "");
    if (a.len() as i32) > 1 {
        println!("{}", a[1 as usize]);
    } else {
        println!("{}", "OK");
    }
}
