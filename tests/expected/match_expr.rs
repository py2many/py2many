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

/* Tiny arithmetic expression parser and evaluator.

Written in the match-as-expression dialect: digit decoding, operator
application and operator precedence are all match expressions, e.g.::

    kind = match code:
        43: PLUS
        45: MINUS
        _: -1

The evaluator itself dispatches on the raw character code with a large
match, as in a classic functional-language lexer. A ``/`` following
another ``/`` is the second half of ``//``, not division: a nested
match tells the two apart::

    kind = match code:
        47: match prev:
            4: -2
            _: SLASH
        40: LPAREN
        _: -1

The parser consumes a list of character codes (``[50, 43, 51]`` is
``"2+3"``) with an iterative shunting-yard evaluator, so the same
source transpiles to both Rust and CPython.
 */

pub const PLUS: i32 = 1;
pub const MINUS: i32 = 2;
pub const STAR: i32 = 3;
pub const SLASH: i32 = 4;
pub const LPAREN: i32 = 5;
pub const RPAREN: i32 = 6;
pub fn digit_value(code: i32) -> i32 {
    return match code {
        48 => 0,
        49 => 1,
        50 => 2,
        51 => 3,
        52 => 4,
        53 => 5,
        54 => 6,
        55 => 7,
        56 => 8,
        57 => 9,
        _ => -1,
    };
}

pub fn apply_op(op: i32, left: i32, right: i32) -> i32 {
    return match op {
        1 => (left + right),
        2 => (left - right),
        3 => (left * right),
        4 => (left / right),
        _ => 0,
    };
}

pub fn precedence(op: i32) -> i32 {
    return match op {
        3 => 2,
        4 => 2,
        1 => 1,
        2 => 1,
        _ => 0,
    };
}

pub fn evaluate(codes: &Vec<i32>) -> i32 {
    let mut values: Vec<i32> = vec![];
    let mut ops: Vec<i32> = vec![];
    let mut nv: i32 = 0;
    let mut no: i32 = 0;
    let mut i: i32 = 0;
    let n = codes.len() as i32;
    let mut prev: i32 = 0;
    while i < (n as i32) {
        let code: i32 = codes[i as usize];
        let kind = match code {
            43 => PLUS,
            45 => MINUS,
            42 => STAR,
            47 => match prev {
                4 => -2,
                _ => SLASH,
            },
            40 => LPAREN,
            41 => RPAREN,
            _ => -1,
        };
        let mut digit: i32 = digit_value(code);
        if digit >= 0 {
            let mut value: i32 = 0;
            while i < (n as i32) {
                digit = digit_value(codes[i as usize]);
                if digit < 0 {
                    break;
                }
                value = ((value * 10) + digit);
                i += 1;
            }
            if nv < (values.len() as i32 as i32) {
                values[nv as usize] = value;
            } else {
                values.push(value);
            }
            nv += 1;
            prev = -1;
            continue;
        }
        if (kind as i32) == -2 {
            i += 1;
            continue;
        }
        if (kind as i32) == LPAREN {
            if no < (ops.len() as i32 as i32) {
                ops[no as usize] = kind;
            } else {
                ops.push(kind);
            }
            no += 1;
        } else {
            if (kind as i32) == RPAREN {
                while no > 0 {
                    if ops[(no - 1) as usize] == LPAREN {
                        break;
                    }
                    nv -= 2;
                    values[nv as usize] = apply_op(
                        ops[(no - 1) as usize],
                        values[nv as usize],
                        values[(nv + 1) as usize],
                    );
                    nv += 1;
                    no -= 1;
                }
                no -= 1;
            } else {
                while no > 0 {
                    if ops[(no - 1) as usize] == LPAREN {
                        break;
                    }
                    if precedence(ops[(no - 1) as usize]) < precedence(kind) {
                        break;
                    }
                    nv -= 2;
                    values[nv as usize] = apply_op(
                        ops[(no - 1) as usize],
                        values[nv as usize],
                        values[(nv + 1) as usize],
                    );
                    nv += 1;
                    no -= 1;
                }
                if no < (ops.len() as i32 as i32) {
                    ops[no as usize] = kind;
                } else {
                    ops.push(kind);
                }
                no += 1;
            }
        }
        prev = kind;
        i += 1;
    }
    while no > 0 {
        nv -= 2;
        values[nv as usize] = apply_op(
            ops[(no - 1) as usize],
            values[nv as usize],
            values[(nv + 1) as usize],
        );
        nv += 1;
        no -= 1;
    }
    return values[0 as usize];
}

pub fn main() -> Result<()> {
    println!("{}", evaluate(&vec![50, 43, 51, 42, 52]));
    println!("{}", evaluate(&vec![40, 50, 43, 51, 41, 42, 52]));
    println!("{}", evaluate(&vec![49, 48, 45, 56, 47, 47, 50]));
    println!("{}", evaluate(&vec![55, 42, 56, 43, 57]));
    println!(
        "{}",
        evaluate(&vec![40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54])
    );
    Ok(())
}
