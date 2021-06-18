
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//! anyhow = "*"
//! structopt = "*"
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
extern crate structopt;
use anyhow::Result;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "fib_with_argparse", about = "Placeholder")]
struct Options {
    #[structopt(short, long)]
    pub v: bool,
    #[structopt(short, long, default_value = "0")]
    pub n: i32,
}

pub fn fib(i: i32) -> i32 {
    if i == 0 || i == 1 {
        return 1;
    }
    return (fib((i - 1)) + fib((i - 2)));
}

pub fn main() -> Result<()> {
    let mut args: _ = Options::from_args();
    if (args.n as i32) == 0 {
        args.n = 5;
    }
    println!("{}", fib(args.n));
    Ok(())
}
