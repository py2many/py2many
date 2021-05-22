
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//! structopt = "*"
//! ```

#![allow(clippy::redundant_static_lifetimes)]
#![allow(clippy::upper_case_acronyms)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

extern crate structopt;
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

pub fn main() {
    let mut args: _ = Options::from_args();
    if (args.n as i32) == 0 {
        args.n = 5;
    }
    println!("{}", fib(args.n));
}
