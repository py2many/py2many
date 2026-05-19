//! ```cargo
//! [package]
//! edition = "2021"
//! [dependencies]
//! anyhow = "*"
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
#![allow(unused_assignments)]
#![allow(unused_variables)]

extern crate anyhow;
use anyhow::Result;

pub fn compare_with_integer_variable() {
    let i: i32 = 0;
    let mut s: i32 = 1;
    if i != 0 {
        s = 2;
    } else {
        s = 3;
    }
    assert!(s == 3);
}

pub fn use_zero_for_comparison() {
    let i: i32 = 0;
    let mut s: i32 = 1;
    if 0 != 0 {
        s = 2;
    } else {
        s = 3;
    }
    assert!(s == 3);
}

pub fn main() -> Result<()> {
    compare_with_integer_variable();
    use_zero_for_comparison();
    println!("{}", "OK");
    Ok(())
}
