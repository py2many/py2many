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
use std::collections::HashMap;

pub fn implicit_keys() -> bool {
    let CODES: &HashMap<&str, i32> = &[("KEY", 1)].iter().cloned().collect::<HashMap<_, _>>();
    return CODES.keys().any(|&x| x == "KEY");
}

pub fn explicit_keys() -> bool {
    let CODES: &HashMap<&str, i32> = &[("KEY", 1)].iter().cloned().collect::<HashMap<_, _>>();
    return CODES.keys().any(|&x| x == "KEY");
}

pub fn dict_values() -> bool {
    let CODES: &HashMap<&str, i32> = &[("KEY", 1)].iter().cloned().collect::<HashMap<_, _>>();
    return CODES.values().any(|&x| x == 1);
}

pub fn return_dict_index_str(key: &str) -> i32 {
    let CODES: &HashMap<&str, i32> = &[("KEY", 1)].iter().cloned().collect::<HashMap<_, _>>();
    return CODES[&key];
}

pub fn return_dict_index_int(key: i32) -> &'static str {
    let CODES: &HashMap<i32, &str> = &[(1, "one")].iter().cloned().collect::<HashMap<_, _>>();
    return CODES[&key] as &'static str;
}

pub fn main() -> Result<()> {
    assert!(implicit_keys());
    assert!(explicit_keys());
    assert!(dict_values());
    assert!(return_dict_index_str("KEY") == 1);
    assert!(return_dict_index_int(1) == "one");
    println!("{}", "OK");
    Ok(())
}
