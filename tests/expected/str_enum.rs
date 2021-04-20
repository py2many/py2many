// cargo-deps: strum,strum_macros

#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

extern crate strum;
extern crate strum_macros;
use std::collections::HashMap;
use strum_macros::{Display, EnumString};

#[derive(Clone, Debug, Display, EnumString, Eq, Hash, PartialEq)]
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
    println!("{}", color_map.len());
}

pub fn main() {
    show();
}
