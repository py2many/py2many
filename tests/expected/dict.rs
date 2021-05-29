
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//!
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

pub fn main() -> Result<(), std::io::Error> {
    assert!(implicit_keys());
    assert!(explicit_keys());
    assert!(dict_values());
    println!("{}", "OK");
    Ok(())
}
