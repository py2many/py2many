//! ```cargo
//! [package]
//! edition = "2021"
//! [dependencies]
//! anyhow = "*"
//! regex = "*"
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
#![allow(unused_variables)]

extern crate anyhow;
extern crate regex;
use anyhow::Result;
use regex::Regex;

pub fn test_re_methods() {
    let text: &'static str = "The quick brown fox jumps over the lazy dog";
    let search_res = Regex::new("fox").unwrap().is_match(text);
    if search_res {
        println!("{}", "Found fox");
    }
    let match_res = Regex::new(&format!("^{}", "The")).unwrap().is_match(text);
    if match_res {
        println!("{}", "Matched The");
    }
    let findall_res = Regex::new("\\w+")
        .unwrap()
        .find_iter(text)
        .map(|m| m.as_str())
        .collect::<Vec<_>>();
    println!("{}", findall_res.len() as i32);
    let sub_res = Regex::new("fox").unwrap().replace_all(text, "cat");
    println!("{}", sub_res);
    let split_res = Regex::new("\\s+").unwrap().split(text).collect::<Vec<_>>();
    println!("{}", split_res.len() as i32);
    let pattern = Regex::new("\\d+").unwrap();
    println!("{}", "Pattern compiled");
}

pub fn main() -> Result<()> {
    test_re_methods();
    Ok(())
}
