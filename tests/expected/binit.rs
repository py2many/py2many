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

pub fn bisect_right(data: &Vec<i32>, item: i32) -> i32 {
    let mut low: i32 = 0;
    let mut high: i32 = data.len() as i32 as i32;
    while low < high {
        let middle: i32 = (((low + high) as f64) / (2 as f64)) as i32;
        if item < data[middle as usize] {
            high = middle;
        } else {
            low = (middle + 1);
        }
    }
    return low;
}

pub fn bin_it(limits: &Vec<i32>, data: &Vec<i32>) -> Vec<i32> {
    let mut bins: &mut Vec<i32> = &mut vec![0];
    for _x in limits {
        bins.push(0);
    }
    for d in data {
        bins[bisect_right(limits, *d) as usize] += 1;
    }
    return bins.to_vec();
}

pub fn main() -> Result<()> {
    let limits: &Vec<i32> = &vec![23, 37, 43, 53, 67, 83];
    let data: &Vec<i32> = &vec![
        95, 21, 94, 12, 99, 4, 70, 75, 83, 93, 52, 80, 57, 5, 53, 86, 65, 17, 92, 83, 71, 61, 54,
        58, 47, 16, 8, 9, 32, 84, 7, 87, 46, 19, 30, 37, 96, 6, 98, 40, 79, 97, 45, 64, 60, 29, 49,
        36, 43, 55,
    ];
    assert!(bin_it(limits, data) == *vec![11, 4, 2, 6, 9, 5, 13]);
    println!("{}", "OK");
    Ok(())
}
