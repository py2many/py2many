
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

/* This file implements a rectangle class  */

pub struct Rectangle {
    pub height: i32,
    pub length: i32,
}

impl Rectangle {
    pub fn is_square(&self) -> bool {
        return self.height == self.length;
    }
}
pub fn show() {
    let mut r: Rectangle = Rectangle {
        height: 1,
        length: 1,
    };
    assert!(r.is_square());
    r = Rectangle {
        height: 1,
        length: 2,
    };
    assert!(!(r.is_square()));
    println!("{}", r.height);
    println!("{}", r.length);
}

pub fn main() {
    show();
}
