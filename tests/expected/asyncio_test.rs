
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//! futures = "*"
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

extern crate futures;
use futures::executor::block_on;

pub async fn nested() -> i32 {
    return 42;
}

pub async fn async_main() {
    assert!((nested().await as i32) == 42);
    println!("{}", "OK");
}

pub fn main() -> Result<(), std::io::Error> {
    block_on(async_main());
    Ok(())
}
