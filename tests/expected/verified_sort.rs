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

pub struct BankAccount {
    pub balance: i32,
}

impl BankAccount {
    pub fn deposit(&self, amount: i32) -> BankAccount {
        return BankAccount {
            balance: ((self.balance as i32) + amount),
        };
    }
}
pub fn safe_sqrt(n: i32) -> i32 {
    let mut i: i32 = 0;
    while (i * i) <= n {
        i += 1;
    }
    return (i - 1);
}

pub fn sqrt_of_9() -> bool {
    return safe_sqrt(9) == 3;
}

pub fn merge(left: &Vec<i32>, right: &Vec<i32>) -> Vec<i32> {
    let mut result: Vec<i32> = vec![];
    let mut i: i32 = 0;
    let mut j: i32 = 0;
    while i < left.len() as i32 && j < right.len() as i32 {
        if left[i as usize] <= right[j as usize] {
            result.push(left[i as usize]);
            i += 1;
        } else {
            result.push(right[j as usize]);
            j += 1;
        }
    }
    while i < (left.len() as i32 as i32) {
        result.push(left[i as usize]);
        i += 1;
    }
    while j < (right.len() as i32 as i32) {
        result.push(right[j as usize]);
        j += 1;
    }
    return result;
}

pub fn take(xs: &Vec<i32>, n: i32) -> Vec<i32> {
    let mut out: Vec<i32> = vec![];
    let mut i: i32 = 0;
    while i < n {
        out.push(xs[i as usize]);
        i += 1;
    }
    return out;
}

pub fn drop(xs: &Vec<i32>, n: i32) -> Vec<i32> {
    let mut out: Vec<i32> = vec![];
    let mut i: i32 = n;
    while i < (xs.len() as i32 as i32) {
        out.push(xs[i as usize]);
        i += 1;
    }
    return out;
}

pub fn sort_u64(arr: &Vec<i32>) -> Vec<i32> {
    if (arr.len() as i32 as i32) <= 1 {
        return arr.to_vec();
    }
    let mid: i32 = ((arr.len() as i32 as i32) / 2);
    let left: Vec<i32> = sort_u64(&take(arr, mid));
    let right: Vec<i32> = sort_u64(&drop(arr, mid));
    return merge(&left, &right);
}

pub fn concrete_example() -> bool {
    return sort_u64(&vec![3, 1, 4, 1, 5, 9, 2, 6]) == vec![1, 1, 2, 3, 4, 5, 6, 9];
}

pub fn main() -> Result<()> {
    let acct: BankAccount = BankAccount { balance: 10 };
    println!("{}", "OK");
    Ok(())
}
