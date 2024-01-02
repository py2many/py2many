//! ```cargo
//! [package]
//! edition = "2021"
//! [dependencies]
//! anyhow = "*"
//! float-ord = "*"
//! ```

#![allow(clippy::assertions_on_constants)]
#![allow(clippy::bool_comparison)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::comparison_to_empty)]
#![allow(clippy::double_parens)] // https://github.com/adsharma/py2many/issues/17
#![allow(clippy::eq_op)]
#![allow(clippy::let_with_type_underscore)]
#![allow(clippy::map_identity)]
#![allow(clippy::needless_return)]
#![allow(clippy::nonminimal_bool)]
#![allow(clippy::partialeq_to_none)]
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

extern crate anyhow;
extern crate float_ord;
use anyhow::Result;
use float_ord::FloatOrd;
use std::cmp;

pub fn default_builtins() {
    let a: &str = "";
    let b: bool = false;
    let c: i32 = 0;
    let d: f64 = 0.0;
    assert!(a == "");
    assert!(b == false);
    assert!(c == 0);
    assert!(d == 0.0);
}

pub fn main() -> Result<()> {
    let a: i32 = cmp::max(1, 2);
    println!("{}", a);
    let b: i32 = cmp::min(1, 2);
    println!("{}", b);
    let c: i32 = cmp::min(FloatOrd(1.0), FloatOrd(2.0)).0 as i32;
    println!("{}", c);
    Ok(())
}
