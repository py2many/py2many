
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//!
//! ```

#![allow(clippy::redundant_static_lifetimes)]
#![allow(clippy::upper_case_acronyms)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

use std::collections::HashMap;

pub fn implicit_keys() -> bool {
    let CODES: &HashMap<&'static str, i32> =
        &[("KEY", 1)].iter().cloned().collect::<HashMap<_, _>>();
    return CODES.keys().any(|&x| x == "KEY");
}

pub fn explicit_keys() -> bool {
    let CODES: &HashMap<&'static str, i32> =
        &[("KEY", 1)].iter().cloned().collect::<HashMap<_, _>>();
    return CODES.keys().any(|&x| x == "KEY");
}

pub fn dict_values() -> bool {
    let CODES: &HashMap<&'static str, i32> =
        &[("KEY", 1)].iter().cloned().collect::<HashMap<_, _>>();
    return CODES.values().any(|&x| x == 1);
}

pub fn main() {
    assert!(implicit_keys());
    assert!(explicit_keys());
    assert!(dict_values());
    println!("{}", "OK");
}
