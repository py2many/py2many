
//! ```cargo
//! [package]
//! edition = "2018"
//! [dependencies]
//!
//! ```

#![allow(clippy::upper_case_acronyms)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_parens)]

use std::collections;
use std::collections::HashMap;
use std::collections::HashSet;

pub fn inline_pass() {
    /* pass */
}

pub fn inline_ellipsis() {
    /* ... */
}

pub fn indexing() -> i32 {
    let mut sum: i32 = 0;
    let mut a: Vec<i32> = vec![];
    for i in (0..10) {
        a.push(i);
        sum += a[i as usize];
    }
    return sum;
}

pub fn infer_bool(code: i32) -> bool {
    return vec![1, 2, 4].iter().any(|&x| x == code);
}

pub fn show() {
    let mut a1: i32 = 10;
    let b1: i32 = 15;
    let b2: _ = 15;
    assert!(b1 == 15);
    assert!((b2 as i32) == 15);
    let b9: i32 = 2;
    let b10: i32 = 2;
    assert!(b9 == b10);
    let a2: f64 = 2.1;
    println!("{}", a2);
    for i in (0..10) {
        println!("{}", i);
    }
    for i in (0..10).step_by(2) {
        println!("{}", i);
    }
    let a3: i32 = -(a1);
    let a4: i32 = (a3 + a1);
    println!("{}", a4);
    let t1: _ = if a1 > 5 { 10 } else { 5 };
    assert!((t1 as i32) == 10);
    let sum1: i32 = indexing();
    println!("{}", sum1);
    let a5: &Vec<i32> = &vec![1, 2, 3];
    println!("{}", a5.len());
    let a9: Vec<&str> = vec!["a", "b", "c", "d"];
    println!("{}", a9.len());
    let a6: &HashSet<i32> = &[1, 2, 3, 4].iter().cloned().collect::<HashSet<_>>();
    println!("{}", a6.len());
    let a7: &HashMap<&str, i32> = &[("a", 1), ("b", 2)]
        .iter()
        .cloned()
        .collect::<HashMap<_, _>>();
    println!("{}", a7.len());
    let a8: bool = true;
    if a8 {
        println!("{}", "true");
    } else {
        if a4 > 0 {
            println!("{}", "never get here");
        }
    }
    if a1 == 11 {
        println!("{}", "false");
    } else {
        println!("{}", "true");
    }
    if Some(1) != None {
        println!("{}", "World is sane");
    }
    println!("{}", if true { "True" } else { "False" });
    if true {
        a1 += 1;
    };
    assert!(a1 == 11);
    if true {
        println!("{}", "true");
    };
    inline_pass();
    let s: &'static str = "1    2";
    println!("{}", s);
    assert!(infer_bool(1));
    let _escape_quotes: &'static str = " foo \"bar\" baz ";
}

pub fn main() {
    show();
}
