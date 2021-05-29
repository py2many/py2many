
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//!
//! ```

#![allow(clippy::collapsible_else_if)]
#![allow(clippy::double_parens)] // https://github.com/adsharma/py2many/issues/17
#![allow(clippy::map_identity)]
#![allow(clippy::needless_return)]
#![allow(clippy::print_literal)]
#![allow(clippy::ptr_arg)]
#![allow(clippy::redundant_static_lifetimes)] // https://github.com/adsharma/py2many/issues/266
#![allow(clippy::unnecessary_cast)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::useless_vec)]
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

pub fn main() -> Result<(), std::io::Error> {
    show();
    Ok(())
}
