
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//! futures = "*"
//! ```

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
    assert!(nested().await as i32 == 42);
    println!("{}", "OK");
}

pub fn main() {
    block_on(async_main());
}
