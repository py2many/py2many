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
use std::collections;

pub fn bubble_sort(seq: &mut Vec<i32>) -> Vec<i32> {
    let L = seq.len() as i32;
    for _ in (0..L) {
        for n in (1..L) {
            if seq[n as usize] < seq[((n as i32) - 1) as usize] {
                ({
                    let (__tmp1, __tmp2) = (seq[n as usize], seq[((n as i32) - 1) as usize]);
                    seq[((n as i32) - 1) as usize] = __tmp1;
                    seq[n as usize] = __tmp2;
                });
            }
        }
    }
    return seq.to_vec();
}

pub fn main() -> Result<()> {
    let mut unsorted: &mut Vec<i32> = &mut vec![14, 11, 19, 5, 16, 10, 19, 12, 5, 12];
    let expected: &Vec<i32> = &vec![5, 5, 10, 11, 12, 12, 14, 16, 19, 19];
    assert!(bubble_sort(unsorted) == *expected);
    println!("{}", "OK");
    Ok(())
}
