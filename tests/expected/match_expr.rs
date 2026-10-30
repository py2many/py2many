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

Written in the match-as-expression dialect, shaped like a classic
functional-language front end. Tokens are a sealed sum type (see
https://github.com/py2many/adt)::

    @sealed
    class Token:
        NUM: None
        PLUS: None
        ...

A ``tokenize`` lexer turns character codes into tokens with a large
match that constructs one variant per arm, and ``evaluate`` dispatches
on the token stream with ``is_*`` checks, e.g.::

    tok = match code:
        43: Token.PLUS()
        47: Token.SLASH()
        _: Token.SKIP()

    for tok in toks:
        if tok.is_skip():
            continue
        elif tok.is_rparen():
            ...

A ``/`` following another ``/`` is the second half of ``//``, not
division: it is skipped before the match when the previous token was a
slash. Numbers are lexed by a second pass (``number_values``) into a
parallel list of values.

Per the static-python rules, fallible functions return ``Result[V, E]``
instead of raising: applying ``//`` to zero yields ``Err``, which the
caller prints with ``unwrap_or``::

    return match op:
        4: Ok(left // right) if right != 0 else Error("Division by zero")
        _: Ok(0)

The parser consumes a list of character codes (``[50, 43, 51]`` is
``"2+3"``), so the same source transpiles to Rust, V and CPython (whose
``match`` statement the python backend emits directly).
 */

pub const PLUS: i32 = 1;
pub const MINUS: i32 = 2;
pub const STAR: i32 = 3;
pub const SLASH: i32 = 4;
pub const LPAREN: i32 = 5;
pub const RPAREN: i32 = 6;
pub enum Token {
    NUM,
    PLUS,
    MINUS,
    STAR,
    SLASH,
    LPAREN,
    RPAREN,
    SKIP,
}

impl Token {
    fn is_num(&self) -> bool {
        matches!(*self, Token::NUM)
    }

    fn is_plus(&self) -> bool {
        matches!(*self, Token::PLUS)
    }

    fn is_minus(&self) -> bool {
        matches!(*self, Token::MINUS)
    }

    fn is_star(&self) -> bool {
        matches!(*self, Token::STAR)
    }

    fn is_slash(&self) -> bool {
        matches!(*self, Token::SLASH)
    }

    fn is_lparen(&self) -> bool {
        matches!(*self, Token::LPAREN)
    }

    fn is_rparen(&self) -> bool {
        matches!(*self, Token::RPAREN)
    }

    fn is_skip(&self) -> bool {
        matches!(*self, Token::SKIP)
    }
}

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

pub fn apply_op(op: i32, left: i32, right: i32) -> Result<i32> {
    return match op {
        1 => Ok((left + right)),
        2 => Ok((left - right)),
        3 => Ok((left * right)),
        4 => {
            if right != 0 {
                Ok((left / right))
            } else {
                Err(anyhow::anyhow!("Division by zero"))
            }
        }
        _ => Ok(0),
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

pub fn number_values(codes: &Vec<i32>) -> Vec<i32> {
    let mut vals: Vec<i32> = vec![];
    let mut i: i32 = 0;
    let n = codes.len() as i32;
    while i < (n as i32) {
        let code: i32 = codes[i as usize];
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
            vals.push(value);
        } else {
            i += 1;
        }
    }
    return vals;
}

pub fn tokenize(codes: &Vec<i32>) -> Vec<Token> {
    let mut toks: Vec<Token> = vec![];
    let mut i: i32 = 0;
    let n = codes.len() as i32;
    let mut prev_slash: bool = false;
    while i < (n as i32) {
        let code: i32 = codes[i as usize];
        if code == 47 && prev_slash {
            i += 1;
            continue;
        }
        let tok = match code {
            48 => Token::NUM,
            49 => Token::NUM,
            50 => Token::NUM,
            51 => Token::NUM,
            52 => Token::NUM,
            53 => Token::NUM,
            54 => Token::NUM,
            55 => Token::NUM,
            56 => Token::NUM,
            57 => Token::NUM,
            43 => Token::PLUS,
            45 => Token::MINUS,
            42 => Token::STAR,
            47 => Token::SLASH,
            40 => Token::LPAREN,
            41 => Token::RPAREN,
            _ => Token::SKIP,
        };
        prev_slash = if !(tok.is_skip()) {
            tok.is_slash()
        } else {
            prev_slash
        };
        toks.push(tok);
        i += 1;
    }
    return toks;
}

pub fn evaluate(codes: &Vec<i32>) -> Result<i32> {
    let toks: Vec<Token> = tokenize(codes);
    let tvals: Vec<i32> = number_values(codes);
    let mut values: Vec<i32> = vec![];
    let mut ops: Vec<i32> = vec![];
    let mut nv: i32 = 0;
    let mut no: i32 = 0;
    let mut k: i32 = 0;
    let mut op: i32;
    let mut r: Result<i32>;
    let mut j: i32 = 0;
    let m = toks.len() as i32;
    while j < (m as i32) {
        if toks[j as usize].is_skip() {
            j += 1;
            continue;
        }
        if toks[j as usize].is_num() {
            while j < (m as i32) {
                if !(toks[j as usize].is_num()) {
                    break;
                }
                j += 1;
            }
            if nv < (values.len() as i32 as i32) {
                values[nv as usize] = tvals[k as usize];
            } else {
                values.push(tvals[k as usize]);
            }
            k += 1;
            nv += 1;
            continue;
        }
        if toks[j as usize].is_lparen() {
            if no < (ops.len() as i32 as i32) {
                ops[no as usize] = LPAREN;
            } else {
                ops.push(LPAREN);
            }
            no += 1;
        } else {
            if toks[j as usize].is_rparen() {
                while no > 0 {
                    if ops[(no - 1) as usize] == LPAREN {
                        break;
                    }
                    nv -= 2;
                    r = apply_op(
                        ops[(no - 1) as usize],
                        values[nv as usize],
                        values[(nv + 1) as usize],
                    );
                    if r.is_ok() {
                        values[nv as usize] = r.unwrap_or(0);
                        nv += 1;
                    } else {
                        return r;
                    }
                    no -= 1;
                }
                no -= 1;
            } else {
                if toks[j as usize].is_plus() {
                    op = PLUS;
                } else {
                    if toks[j as usize].is_minus() {
                        op = MINUS;
                    } else {
                        if toks[j as usize].is_star() {
                            op = STAR;
                        } else {
                            op = SLASH;
                        }
                    }
                }
                while no > 0 {
                    if ops[(no - 1) as usize] == LPAREN {
                        break;
                    }
                    if precedence(ops[(no - 1) as usize]) < precedence(op) {
                        break;
                    }
                    nv -= 2;
                    r = apply_op(
                        ops[(no - 1) as usize],
                        values[nv as usize],
                        values[(nv + 1) as usize],
                    );
                    if r.is_ok() {
                        values[nv as usize] = r.unwrap_or(0);
                        nv += 1;
                    } else {
                        return r;
                    }
                    no -= 1;
                }
                if no < (ops.len() as i32 as i32) {
                    ops[no as usize] = op;
                } else {
                    ops.push(op);
                }
                no += 1;
            }
        }
        j += 1;
    }
    while no > 0 {
        nv -= 2;
        r = apply_op(
            ops[(no - 1) as usize],
            values[nv as usize],
            values[(nv + 1) as usize],
        );
        if r.is_ok() {
            values[nv as usize] = r.unwrap_or(0);
            nv += 1;
        } else {
            return r;
        }
        no -= 1;
    }
    if nv == 0 {
        return Err(anyhow::anyhow!("empty expression"));
    }
    return Ok(values[0 as usize]);
}

pub fn main() -> Result<()> {
    println!("{}", evaluate(&vec![50, 43, 51, 42, 52]).unwrap_or(-999));
    println!(
        "{}",
        evaluate(&vec![40, 50, 43, 51, 41, 42, 52]).unwrap_or(-999)
    );
    println!(
        "{}",
        evaluate(&vec![49, 48, 45, 56, 47, 47, 50]).unwrap_or(-999)
    );
    println!("{}", evaluate(&vec![55, 42, 56, 43, 57]).unwrap_or(-999));
    println!(
        "{}",
        evaluate(&vec![40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54]).unwrap_or(-999)
    );
    println!("{}", evaluate(&vec![49, 48, 47, 48]).unwrap_or(-999));
    Ok(())
}
