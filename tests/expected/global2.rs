//! ```cargo
//! [package]
//! edition = "2021"
//! [dependencies]
//! anyhow = "*"
//! lazy_static = "*"
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
extern crate lazy_static;
use anyhow::Result;
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::collections::HashSet;

pub const code_0: i32 = 0;
pub const code_1: i32 = 1;
pub const code_a: &'static str = "a";
pub const code_b: &'static str = "b";
lazy_static! {
    pub static ref l_b: HashSet<&'static str> = [code_a].iter().cloned().collect::<HashSet<_>>();
}
lazy_static! {
    pub static ref l_c: HashMap<&'static str, i32> = [(code_b, code_0)]
        .iter()
        .cloned()
        .collect::<HashMap<_, _>>();
}
pub fn main() -> Result<()> {
    assert!(l_b.iter().any(|&x| x == "a"));
    println!("{}", "OK");
    Ok(())
}
