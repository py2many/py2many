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
use std::collections::HashMap;

/* Tiny arithmetic expression parser and evaluator.

Written in the match-as-expression dialect, shaped like a classic
functional-language front end. Tokens are a sealed sum type (see
https://github.com/py2many/adt)::

    @sealed
    class Token:
        NUM: None
        PLUS: None
        ...

and the parsed program is a recursive expression tree::

    @sealed
    class Expr:
        NUMBER: float
        VARIABLE: str
        ADD: BinOp
        ...

A ``tokenize`` lexer turns character codes into tokens with a large
match that constructs one variant per arm, a ``parse`` shunting-yard
pass builds the tree, and a recursive ``eval_expr`` evaluates it by
dispatching on variant with ``is_*`` checks, e.g.::

    tok = match code:
        43: Token.PLUS()
        47: Token.SLASH()
        _: Token.SKIP()

    j = 0
    while j < m:  # indexed: binding tokens would move them in Rust
        ...

    if e.is_add():
        b_add = e.add()
        return combine(PLUS, eval_expr(b_add.left, env), eval_expr(b_add.right, env))

A ``/`` following another ``/`` is the second half of ``//``, not
division: it is skipped before the match when the previous token was a
slash. Numbers are lexed by a second pass (``number_values``) into a
parallel list of values.

Per the static-python rules, fallible functions return ``Result[V, E]``
instead of raising: applying ``//`` to zero yields ``Err``, an unknown
variable yields ``Err``, and the caller prints with ``unwrap_or``::

    return match op:
        4: Ok(left / right) if right != 0.0 else Error("Division by zero")
        _: Ok(0.0)

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
#[derive(Clone)]
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

#[derive(Clone)]
pub struct BinOp {
    pub left: Box<Expr>,
    pub right: Box<Expr>,
}

impl BinOp {}
#[derive(Clone)]
pub enum Expr {
    NUMBER(f64),
    VARIABLE(String),
    ADD(BinOp),
    SUBTRACT(BinOp),
    MULTIPLY(BinOp),
    DIVIDE(BinOp),
}

impl Expr {
    fn number(&self) -> f64 {
        if let Expr::NUMBER(val) = self {
            *val
        } else {
            panic!("not a NUMBER")
        }
    }

    fn variable(&self) -> &String {
        if let Expr::VARIABLE(val) = self {
            val
        } else {
            panic!("not a VARIABLE")
        }
    }

    fn add(&self) -> &BinOp {
        if let Expr::ADD(val) = self {
            val
        } else {
            panic!("not a ADD")
        }
    }

    fn subtract(&self) -> &BinOp {
        if let Expr::SUBTRACT(val) = self {
            val
        } else {
            panic!("not a SUBTRACT")
        }
    }

    fn multiply(&self) -> &BinOp {
        if let Expr::MULTIPLY(val) = self {
            val
        } else {
            panic!("not a MULTIPLY")
        }
    }

    fn divide(&self) -> &BinOp {
        if let Expr::DIVIDE(val) = self {
            val
        } else {
            panic!("not a DIVIDE")
        }
    }

    fn is_number(&self) -> bool {
        matches!(*self, Expr::NUMBER(_))
    }

    fn is_variable(&self) -> bool {
        matches!(*self, Expr::VARIABLE(_))
    }

    fn is_add(&self) -> bool {
        matches!(*self, Expr::ADD(_))
    }

    fn is_subtract(&self) -> bool {
        matches!(*self, Expr::SUBTRACT(_))
    }

    fn is_multiply(&self) -> bool {
        matches!(*self, Expr::MULTIPLY(_))
    }

    fn is_divide(&self) -> bool {
        matches!(*self, Expr::DIVIDE(_))
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

pub fn apply_float(op: i32, left: f64, right: f64) -> Result<f64> {
    return match op {
        1 => Ok((left + right)),
        2 => Ok((left - right)),
        3 => Ok((left * right)),
        4 => {
            if right != 0.0 {
                Ok((left / right))
            } else {
                Err(anyhow::anyhow!("Division by zero"))
            }
        }
        _ => Ok(0.0),
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

pub fn number_values(codes: &Vec<i32>) -> Vec<f64> {
    let mut vals: Vec<f64> = vec![];
    let mut i: i32 = 0;
    let n = codes.len() as i32;
    while i < (n as i32) {
        let code: i32 = codes[i as usize];
        let mut digit: i32 = digit_value(code);
        if digit >= 0 {
            let mut value: f64 = 0.0;
            while i < (n as i32) {
                digit = digit_value(codes[i as usize]);
                if digit < 0 {
                    break;
                }
                value = ((value * 10.0) + digit as f64);
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

pub fn lookup(env: &HashMap<&str, f64>, name: &str) -> Result<f64> {
    if env.contains_key(&name) {
        return Ok(env[&name]);
    }
    return Err(anyhow::anyhow!("undefined variable"));
}

pub fn combine(op: i32, l: Result<f64>, r: Result<f64>) -> Result<f64> {
    if l.is_ok() {
        if r.is_ok() {
            return apply_float(op, l.unwrap_or(0.0), r.unwrap_or(0.0));
        }
        return r;
    }
    return l;
}

pub fn make_node(op: i32, left: &Expr, right: &Expr) -> Expr {
    return match op {
        1 => Expr::ADD(BinOp {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        2 => Expr::SUBTRACT(BinOp {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        3 => Expr::MULTIPLY(BinOp {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        4 => Expr::DIVIDE(BinOp {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }),
        _ => Expr::NUMBER(0.0),
    };
}

pub fn eval_expr(e: &Expr, env: &HashMap<&str, f64>) -> Result<f64> {
    if e.is_number() {
        return Ok(e.number());
    } else {
        if e.is_variable() {
            return lookup(env, e.variable());
        } else {
            if e.is_add() {
                let b_add = e.add();
                return combine(
                    PLUS,
                    eval_expr(&b_add.left, env),
                    eval_expr(&b_add.right, env),
                );
            } else {
                if e.is_subtract() {
                    let b_subtract = e.subtract();
                    return combine(
                        MINUS,
                        eval_expr(&b_subtract.left, env),
                        eval_expr(&b_subtract.right, env),
                    );
                } else {
                    if e.is_multiply() {
                        let b_multiply = e.multiply();
                        return combine(
                            STAR,
                            eval_expr(&b_multiply.left, env),
                            eval_expr(&b_multiply.right, env),
                        );
                    } else {
                        if e.is_divide() {
                            let b_divide = e.divide();
                            return combine(
                                SLASH,
                                eval_expr(&b_divide.left, env),
                                eval_expr(&b_divide.right, env),
                            );
                        } else {
                            return Err(anyhow::anyhow!("unknown expression"));
                        }
                    }
                }
            }
        }
    }
}

pub fn parse(toks: &Vec<Token>, tvals: &Vec<f64>) -> Vec<Expr> {
    let mut nodes: Vec<Expr> = vec![];
    let mut ops: Vec<i32> = vec![];
    let mut nv: i32 = 0;
    let mut no: i32 = 0;
    let mut k: i32 = 0;
    let mut j: i32 = 0;
    let m = toks.len() as i32;
    let mut op: i32;
    let mut node: Expr;
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
            if nv < (nodes.len() as i32 as i32) {
                nodes[nv as usize] = Expr::NUMBER(tvals[k as usize]);
            } else {
                nodes.push(Expr::NUMBER(tvals[k as usize]));
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
                    node = make_node(
                        ops[(no - 1) as usize],
                        &nodes[nv as usize],
                        &nodes[(nv + 1) as usize],
                    );
                    if nv < (nodes.len() as i32 as i32) {
                        nodes[nv as usize] = node;
                    } else {
                        nodes.push(node);
                    }
                    nv += 1;
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
                    node = make_node(
                        ops[(no - 1) as usize],
                        &nodes[nv as usize],
                        &nodes[(nv + 1) as usize],
                    );
                    if nv < (nodes.len() as i32 as i32) {
                        nodes[nv as usize] = node;
                    } else {
                        nodes.push(node);
                    }
                    nv += 1;
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
        node = make_node(
            ops[(no - 1) as usize],
            &nodes[nv as usize],
            &nodes[(nv + 1) as usize],
        );
        if nv < (nodes.len() as i32 as i32) {
            nodes[nv as usize] = node;
        } else {
            nodes.push(node);
        }
        nv += 1;
        no -= 1;
    }
    return nodes;
}

pub fn evaluate(codes: &Vec<i32>, env: &HashMap<&str, f64>) -> Result<f64> {
    let toks: &Vec<Token> = &tokenize(codes);
    let tvals: &Vec<f64> = &number_values(codes);
    let nodes: &Vec<Expr> = &parse(toks, tvals);
    if (nodes.len() as i32 as i32) == 0 {
        return Err(anyhow::anyhow!("empty expression"));
    }
    return eval_expr(&nodes[0 as usize], env);
}

pub fn main() -> Result<()> {
    let env: HashMap<&str, f64> = [("x", 5.0)].iter().cloned().collect::<HashMap<_, _>>();
    println!(
        "{}",
        evaluate(&vec![50, 43, 51, 42, 52], &env).unwrap_or(-999.0) as i32
    );
    println!(
        "{}",
        evaluate(&vec![40, 50, 43, 51, 41, 42, 52], &env).unwrap_or(-999.0) as i32
    );
    println!(
        "{}",
        evaluate(&vec![49, 48, 45, 56, 47, 47, 50], &env).unwrap_or(-999.0) as i32
    );
    println!(
        "{}",
        evaluate(&vec![55, 42, 56, 43, 57], &env).unwrap_or(-999.0) as i32
    );
    println!(
        "{}",
        evaluate(&vec![40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54], &env).unwrap_or(-999.0) as i32
    );
    println!(
        "{}",
        evaluate(&vec![49, 48, 47, 48], &env).unwrap_or(-999.0) as i32
    );
    println!(
        "{}",
        eval_expr(
            &Expr::ADD(BinOp {
                left: Box::new(Expr::VARIABLE("x".to_string()).clone()),
                right: Box::new(Expr::NUMBER(1.0).clone())
            }),
            &env
        )
        .unwrap_or(-999.0) as i32
    );
    Ok(())
}
