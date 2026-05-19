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
use std::collections;

pub fn test_str_methods() {
    let s: &'static str = "  Hello World  ";
    println!("{}", s.to_lowercase());
    println!("{}", s.to_uppercase());
    println!("{}", {
        let mut c = s.chars();
        match c.next() {
            None => String::new(),
            Some(f) => f.to_uppercase().collect::<String>() + &c.as_str().to_lowercase(),
        }
    });
    println!("{}", s.trim());
    println!("{}", s.trim_start());
    println!("{}", s.trim_end());
    let parts = s.split_whitespace().collect::<Vec<_>>();
    println!("{}", format!("{:?}", parts).replace("\"", "'"));
    let joined = vec!["a", "b", "c"].join("-");
    println!("{}", joined);
    println!("{}", s.find("World").map_or(-1, |i| i as i32));
    println!("{}", s.replace("World", "Vlang"));
    if "123".chars().all(|c| c.is_ascii_digit()) {
        println!("{}", "digit");
    }
    if "abc".chars().all(|c| c.is_alphabetic()) {
        println!("{}", "alpha");
    }
    if "   ".chars().all(|c| c.is_whitespace()) {
        println!("{}", "space");
    }
}

pub fn main() -> Result<()> {
    test_str_methods();
    Ok(())
}
