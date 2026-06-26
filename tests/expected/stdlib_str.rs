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
#![allow(clippy::const_is_empty)]

extern crate anyhow;
use anyhow::Result;
use std::collections;

pub fn str_methods() {
    let s: &'static str = "  Hello World  ";
    println!("{}", s.to_lowercase());
    println!("{}", s.to_uppercase());
    println!("{}", {
        let mut __c = s.chars();
        match __c.next() {
            Some(__f) => __f.to_uppercase().collect::<String>() + &__c.as_str().to_lowercase(),
            None => String::new(),
        }
    });
    println!("{}", s.trim());
    println!("{}", s.trim_start());
    println!("{}", s.trim_end());
    let parts: &Vec<&str> = &s.split_whitespace().collect::<Vec<&str>>();
    println!(
        "[{}]",
        parts
            .iter()
            .map(|__x| format!("'{}'", __x))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let joined = vec!["a", "b", "c"].join("-");
    println!("{}", joined);
    println!("{}", s.find("World").map(|i| i as i32).unwrap_or(-1));
    println!("{}", s.replace("World", "Vlang"));
    if (!"123".is_empty() && "123".chars().all(|c| c.is_ascii_digit())) {
        println!("{}", "digit");
    }
    if (!"abc".is_empty() && "abc".chars().all(|c| c.is_alphabetic())) {
        println!("{}", "alpha");
    }
    if (!"   ".is_empty() && "   ".chars().all(|c| c.is_whitespace())) {
        println!("{}", "space");
    }
}

pub fn main() -> Result<()> {
    str_methods();
    Ok(())
}
