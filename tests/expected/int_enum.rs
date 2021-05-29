
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//! flagset = "*"
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

extern crate flagset;
use flagset::flags;
use std::collections::HashMap;
use std::os::raw::c_int;

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum Colors {
    RED,
    GREEN,
    BLUE,
}

flags! {
    pub enum Permissions: c_int {
        R = 1,
        W = 2,
        X = 16,
    }
}

pub fn show() {
    let color_map: &HashMap<Colors, &str> = &[
        (Colors::RED, "red"),
        (Colors::GREEN, "green"),
        (Colors::BLUE, "blue"),
    ]
    .iter()
    .cloned()
    .collect::<HashMap<_, _>>();
    let a: Colors = Colors::GREEN;
    if a == Colors::GREEN {
        println!("{}", "green");
    } else {
        println!("{}", "Not green");
    }
    let b: Permissions = Permissions::R;
    if b == Permissions::R {
        println!("{}", "R");
    } else {
        println!("{}", "Not R");
    }
    assert!((color_map.len() as i32) != 0);
}

pub fn main() -> Result<(), std::io::Error> {
    show();
    Ok(())
}
