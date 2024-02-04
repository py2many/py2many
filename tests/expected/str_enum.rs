//! ```cargo
//! [package]
//! edition = "2021"
//! [dependencies]
//! anyhow = "*"
//! strum = "*"
//! strum_macros = "*"
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
extern crate strum;
extern crate strum_macros;
use anyhow::Result;
use std::collections::HashMap;
use strum_macros::{Display, EnumString, VariantNames};

#[derive(Clone, Debug, Display, EnumString, VariantNames, Eq, Hash, PartialEq)]
pub enum Colors {
    #[strum(serialize = "red")]
    RED,
    #[strum(serialize = "green")]
    GREEN,
    #[strum(serialize = "blue")]
    BLUE,
}

pub fn show() {
    let color_map: &HashMap<Colors, &str> = &[
        (Colors::RED, "1"),
        (Colors::GREEN, "2"),
        (Colors::BLUE, "3"),
    ]
    .iter()
    .cloned()
    .collect::<HashMap<_, _>>();
    let a: Colors = Colors::GREEN;
    if a == Colors::GREEN {
        println!("{}", "green");
    } else {
        println!("{}", "Not green");
    }
    println!("{}", color_map.len() as i32);
}

pub fn main() -> Result<()> {
    show();
    Ok(())
}
