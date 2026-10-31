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
#![allow(dead_code)]
#![allow(unreachable_patterns)]
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
        NUM: int = '0'
        PLUS: int = '+'
        ...

and the parsed program is a recursive expression tree::

    @sealed
    class Expr:
        NUMBER: float
        VARIABLE: str
        ADD(Expr, Expr)
        ...

A ``tokenize`` lexer turns character codes into tokens with a large
match that constructs one variant per arm, a ``parse`` shunting-yard
pass builds the tree, and a recursive ``eval_expr`` evaluates it by
matching on variant with bindings, e.g.::

    return match e:
        Expr.NUMBER(n): Ok(n)
        Expr.ADD(l, r): apply_float(Token.PLUS(), eval_expr(l, env), eval_expr(r, env))

``ops`` are ``Token``s themselves, not integer codes: there are no
``PLUS = 1`` style constants. ``precedence``, ``apply_float`` and
``make_node`` all take a ``Token`` and match on its variant::

    return match op:
        Token.PLUS(): Expr.ADD(left, right)
        _: Expr.NUMBER(0.0)

Character literals (``'+'``, ``')'``, ``'0'``) stand for their codes:
no magic numbers appear. Token payloads default to their
representative character, so constructions stay nullary
(``Token.PLUS()`` means ``Token.PLUS('+')``).

A ``/`` following another ``/`` is the second half of ``//``, not
division: it is skipped before the match when the previous token was a
slash. Numbers are lexed by a second pass (``number_values``) into a
parallel list of values.

Per the static-python rules, fallible functions return ``Result[V, E]``
instead of raising: applying ``//`` to zero yields ``Err``, an unknown
variable yields ``Err``, and the caller prints with ``unwrap_or``::

    return match op:
        Token.SLASH(): Ok(left / right) if right != 0.0 else Error("Division by zero")
        _: Ok(0.0)

The parser consumes a list of character codes (``[50, 43, 51]`` is
``"2+3"``), so the same source transpiles to Rust, V and CPython (whose
``match`` statement the python backend emits directly).
 */

#[derive(Clone, Copy)]
pub enum Token {
    NUM(i32),
    PLUS(i32),
    MINUS(i32),
    STAR(i32),
    SLASH(i32),
    LPAREN(i32),
    RPAREN(i32),
    SKIP(i32),
}

impl Token {
    fn num(&self) -> i32 {
        if let Token::NUM(val) = self {
            *val
        } else {
            panic!("not a NUM")
        }
    }

    fn plus(&self) -> i32 {
        if let Token::PLUS(val) = self {
            *val
        } else {
            panic!("not a PLUS")
        }
    }

    fn minus(&self) -> i32 {
        if let Token::MINUS(val) = self {
            *val
        } else {
            panic!("not a MINUS")
        }
    }

    fn star(&self) -> i32 {
        if let Token::STAR(val) = self {
            *val
        } else {
            panic!("not a STAR")
        }
    }

    fn slash(&self) -> i32 {
        if let Token::SLASH(val) = self {
            *val
        } else {
            panic!("not a SLASH")
        }
    }

    fn lparen(&self) -> i32 {
        if let Token::LPAREN(val) = self {
            *val
        } else {
            panic!("not a LPAREN")
        }
    }

    fn rparen(&self) -> i32 {
        if let Token::RPAREN(val) = self {
            *val
        } else {
            panic!("not a RPAREN")
        }
    }

    fn skip(&self) -> i32 {
        if let Token::SKIP(val) = self {
            *val
        } else {
            panic!("not a SKIP")
        }
    }

    fn is_num(&self) -> bool {
        matches!(*self, Token::NUM(_))
    }

    fn is_plus(&self) -> bool {
        matches!(*self, Token::PLUS(_))
    }

    fn is_minus(&self) -> bool {
        matches!(*self, Token::MINUS(_))
    }

    fn is_star(&self) -> bool {
        matches!(*self, Token::STAR(_))
    }

    fn is_slash(&self) -> bool {
        matches!(*self, Token::SLASH(_))
    }

    fn is_lparen(&self) -> bool {
        matches!(*self, Token::LPAREN(_))
    }

    fn is_rparen(&self) -> bool {
        matches!(*self, Token::RPAREN(_))
    }

    fn is_skip(&self) -> bool {
        matches!(*self, Token::SKIP(_))
    }
}

#[derive(Clone)]
pub enum Expr {
    NUMBER(f64),
    VARIABLE(String),
    ADD(Box<Expr>, Box<Expr>),
    SUBTRACT(Box<Expr>, Box<Expr>),
    MULTIPLY(Box<Expr>, Box<Expr>),
    DIVIDE(Box<Expr>, Box<Expr>),
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

    fn add(&self) -> (Box<Expr>, Box<Expr>) {
        if let Expr::ADD(v0, v1) = self {
            (v0.clone(), v1.clone())
        } else {
            panic!("not a ADD")
        }
    }

    fn subtract(&self) -> (Box<Expr>, Box<Expr>) {
        if let Expr::SUBTRACT(v0, v1) = self {
            (v0.clone(), v1.clone())
        } else {
            panic!("not a SUBTRACT")
        }
    }

    fn multiply(&self) -> (Box<Expr>, Box<Expr>) {
        if let Expr::MULTIPLY(v0, v1) = self {
            (v0.clone(), v1.clone())
        } else {
            panic!("not a MULTIPLY")
        }
    }

    fn divide(&self) -> (Box<Expr>, Box<Expr>) {
        if let Expr::DIVIDE(v0, v1) = self {
            (v0.clone(), v1.clone())
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
        matches!(*self, Expr::ADD(_, _))
    }

    fn is_subtract(&self) -> bool {
        matches!(*self, Expr::SUBTRACT(_, _))
    }

    fn is_multiply(&self) -> bool {
        matches!(*self, Expr::MULTIPLY(_, _))
    }

    fn is_divide(&self) -> bool {
        matches!(*self, Expr::DIVIDE(_, _))
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

pub fn apply_float(op: &Token, l: Result<f64>, r: Result<f64>) -> Result<f64> {
    if l.is_ok() {
        if r.is_ok() {
            let left = l.unwrap_or(0.0);
            let right = r.unwrap_or(0.0);
            return match op {
                Token::PLUS(_) => Ok((left + right)),
                Token::MINUS(_) => Ok((left - right)),
                Token::STAR(_) => Ok((left * right)),
                Token::SLASH(_) => {
                    if (right as f64) != 0.0 {
                        Ok((left / right))
                    } else {
                        Err(anyhow::anyhow!("Division by zero"))
                    }
                }
                _ => Ok(0.0),
            };
        }
        return r;
    }
    return l;
}

pub fn precedence(op: &Token) -> i32 {
    return match op {
        Token::STAR(_) => 2,
        Token::SLASH(_) => 2,
        Token::PLUS(_) => 1,
        Token::MINUS(_) => 1,
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
            48 => Token::NUM(48),
            49 => Token::NUM(48),
            50 => Token::NUM(48),
            51 => Token::NUM(48),
            52 => Token::NUM(48),
            53 => Token::NUM(48),
            54 => Token::NUM(48),
            55 => Token::NUM(48),
            56 => Token::NUM(48),
            57 => Token::NUM(48),
            43 => Token::PLUS(43),
            45 => Token::MINUS(45),
            42 => Token::STAR(42),
            47 => Token::SLASH(47),
            40 => Token::LPAREN(40),
            41 => Token::RPAREN(41),
            _ => Token::SKIP(0),
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

pub fn make_node(op: &Token, left: &Expr, right: &Expr) -> Expr {
    return match op {
        Token::PLUS(_) => Expr::ADD(Box::new(left.clone()), Box::new(right.clone())),
        Token::MINUS(_) => Expr::SUBTRACT(Box::new(left.clone()), Box::new(right.clone())),
        Token::STAR(_) => Expr::MULTIPLY(Box::new(left.clone()), Box::new(right.clone())),
        Token::SLASH(_) => Expr::DIVIDE(Box::new(left.clone()), Box::new(right.clone())),
        _ => Expr::NUMBER(0.0),
    };
}

pub fn eval_expr(e: &Expr, env: &HashMap<&str, f64>) -> Result<f64> {
    return match e {
        Expr::NUMBER(n) => Ok(*n),
        Expr::VARIABLE(name) => lookup(env, name),
        Expr::ADD(l, r) => apply_float(&Token::PLUS(43), eval_expr(l, env), eval_expr(r, env)),
        Expr::SUBTRACT(l, r) => {
            apply_float(&Token::MINUS(45), eval_expr(l, env), eval_expr(r, env))
        }
        Expr::MULTIPLY(l, r) => apply_float(&Token::STAR(42), eval_expr(l, env), eval_expr(r, env)),
        Expr::DIVIDE(l, r) => apply_float(&Token::SLASH(47), eval_expr(l, env), eval_expr(r, env)),
        _ => Err(anyhow::anyhow!("unknown expression")),
    };
}

pub fn parse(toks: &Vec<Token>, tvals: &Vec<f64>) -> Vec<Expr> {
    let mut nodes: Vec<Expr> = vec![];
    let mut ops: Vec<Token> = vec![];
    let mut nv: i32 = 0;
    let mut no: i32 = 0;
    let mut k: i32 = 0;
    let mut j: i32 = 0;
    let m = toks.len() as i32;
    let mut op: Token;
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
                ops[no as usize] = Token::LPAREN(40);
            } else {
                ops.push(Token::LPAREN(40));
            }
            no += 1;
        } else {
            if toks[j as usize].is_rparen() {
                while no > 0 {
                    if ops[(no - 1) as usize].is_lparen() {
                        break;
                    }
                    nv -= 2;
                    node = make_node(
                        &ops[(no - 1) as usize],
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
                op = toks[j as usize];
                while no > 0 {
                    if ops[(no - 1) as usize].is_lparen() {
                        break;
                    }
                    if precedence(&ops[(no - 1) as usize]) < precedence(&op) {
                        break;
                    }
                    nv -= 2;
                    node = make_node(
                        &ops[(no - 1) as usize],
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
            &ops[(no - 1) as usize],
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
            &Expr::ADD(
                Box::new(Expr::VARIABLE("x".to_string()).clone()),
                Box::new(Expr::NUMBER(1.0).clone())
            ),
            &env
        )
        .unwrap_or(-999.0) as i32
    );
    Ok(())
}
