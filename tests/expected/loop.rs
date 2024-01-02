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

extern crate anyhow;
use anyhow::Result;

pub fn for_with_break() {
    for i in (0..4) {
        if (i as i32) == 2 {
            break;
        }
        println!("{}", i);
    }
}

pub fn for_with_continue() {
    for i in (0..4) {
        if (i as i32) == 2 {
            continue;
        }
        println!("{}", i);
    }
}

pub fn for_with_else() {
    let has_break: bool = false;
    for i in (0..4) {
        println!("{}", i);
    }
    if has_break != true {
        println!("{}", "OK");
    }
}

pub fn while_with_break() {
    let mut i: i32 = 0;
    loop {
        if i == 2 {
            break;
        }
        println!("{}", i);
        i += 1;
    }
}

pub fn while_with_continue() {
    let mut i: i32 = 0;
    while i < 5 {
        i += 1;
        if i == 2 {
            continue;
        }
        println!("{}", i);
    }
}

pub fn main() -> Result<()> {
    for_with_break();
    for_with_continue();
    for_with_else();
    while_with_break();
    while_with_continue();
    Ok(())
}
