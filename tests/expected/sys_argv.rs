
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//! anyhow = "*"
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

extern crate anyhow;
use anyhow::Result;
use std::env;

pub fn main() -> Result<()> {
    let a: Vec<&str> = env::args()
        .map(|s| &*Box::leak(s.into_boxed_str()))
        .collect();
    let cmd: &str = a[0 as usize];
    if cmd == "dart" {
        /* pass */
    } else {
        assert!(cmd.contains("sys_argv"));
    }
    if (a.len() as i32) > 1 {
        println!("{}", a[1 as usize]);
    } else {
        println!("{}", "OK");
    }
    Ok(())
}
