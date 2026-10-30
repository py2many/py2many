@[translated]
module main

struct Result[T] {
	val   T
	err   string
	is_ok bool
}

fn (r Result[T]) is_ok() bool {
	return r.is_ok
}

fn (r Result[T]) unwrap() T {
	if r.is_ok {
		return r.val
	}
	panic(r.err)
}

fn (r Result[T]) unwrap_or(default T) T {
	if r.is_ok {
		return r.val
	}
	return default
}

// Tiny arithmetic expression parser and evaluator.
//
// Written in the match-as-expression dialect, shaped like a classic
// functional-language front end. Tokens are a sealed sum type (see
// https://github.com/py2many/adt)::
//
//     @sealed
//     class Token:
//         NUM: None
//         PLUS: None
//         ...
//
// and the parsed program is a recursive expression tree::
//
//     @sealed
//     class Expr:
//         NUMBER: float
//         VARIABLE: str
//         ADD: BinOp
//         ...
//
// A ``tokenize`` lexer turns character codes into tokens with a large
// match that constructs one variant per arm, a ``parse`` shunting-yard
// pass builds the tree, and a recursive ``eval_expr`` evaluates it by
// dispatching on variant with ``is_*`` checks, e.g.::
//
//     tok = match code:
//         43: Token.PLUS()
//         47: Token.SLASH()
//         _: Token.SKIP()
//
//     j = 0
//     while j < m:  # indexed: binding tokens would move them in Rust
//         ...
//
//     if e.is_add():
//         b_add = e.add()
//         return combine(PLUS, eval_expr(b_add.left, env), eval_expr(b_add.right, env))
//
// A ``/`` following another ``/`` is the second half of ``//``, not
// division: it is skipped before the match when the previous token was a
// slash. Numbers are lexed by a second pass (``number_values``) into a
// parallel list of values.
//
// Per the static-python rules, fallible functions return ``Result[V, E]``
// instead of raising: applying ``//`` to zero yields ``Err``, an unknown
// variable yields ``Err``, and the caller prints with ``unwrap_or``::
//
//     return match op:
//         4: Ok(left / right) if right != 0.0 else Error("Division by zero")
//         _: Ok(0.0)
//
// The parser consumes a list of character codes (``[50, 43, 51]`` is
// ``"2+3"``), so the same source transpiles to Rust, V and CPython (whose
// ``match`` statement the python backend emits directly).

const plus = 1
const minus = 2
const star = 3
const slash = 4
const lparen = 5
const rparen = 6

struct TokenNum {}

struct TokenPlus {}

struct TokenMinus {}

struct TokenStar {}

struct TokenSlash {}

struct TokenLparen {}

struct TokenRparen {}

struct TokenSkip {}

type Token = TokenNum
	| TokenPlus
	| TokenMinus
	| TokenStar
	| TokenSlash
	| TokenLparen
	| TokenRparen
	| TokenSkip

fn (t Token) is_num() bool {
	return t is TokenNum
}

fn (t Token) is_plus() bool {
	return t is TokenPlus
}

fn (t Token) is_minus() bool {
	return t is TokenMinus
}

fn (t Token) is_star() bool {
	return t is TokenStar
}

fn (t Token) is_slash() bool {
	return t is TokenSlash
}

fn (t Token) is_lparen() bool {
	return t is TokenLparen
}

fn (t Token) is_rparen() bool {
	return t is TokenRparen
}

fn (t Token) is_skip() bool {
	return t is TokenSkip
}

pub struct BinOp {
pub mut:
	left  Expr
	right Expr
}

struct ExprAdd {
	left  Expr
	right Expr
}

struct ExprSubtract {
	left  Expr
	right Expr
}

struct ExprMultiply {
	left  Expr
	right Expr
}

struct ExprDivide {
	left  Expr
	right Expr
}

type Expr = f64 | string | ExprAdd | ExprSubtract | ExprMultiply | ExprDivide

fn (e Expr) is_number() bool {
	return e is f64
}

fn (e Expr) number() f64 {
	if e is f64 {
		return e
	}
	panic('not a NUMBER')
}

fn (e Expr) is_variable() bool {
	return e is string
}

fn (e Expr) variable() string {
	if e is string {
		return e
	}
	panic('not a VARIABLE')
}

fn (e Expr) is_add() bool {
	return e is ExprAdd
}

fn (e Expr) add() ExprAdd {
	if e is ExprAdd {
		return e
	}
	panic('not a ADD')
}

fn (e Expr) is_subtract() bool {
	return e is ExprSubtract
}

fn (e Expr) subtract() ExprSubtract {
	if e is ExprSubtract {
		return e
	}
	panic('not a SUBTRACT')
}

fn (e Expr) is_multiply() bool {
	return e is ExprMultiply
}

fn (e Expr) multiply() ExprMultiply {
	if e is ExprMultiply {
		return e
	}
	panic('not a MULTIPLY')
}

fn (e Expr) is_divide() bool {
	return e is ExprDivide
}

fn (e Expr) divide() ExprDivide {
	if e is ExprDivide {
		return e
	}
	panic('not a DIVIDE')
}

fn digit_value(code int) int {
	return match code {
		48 { 0 }
		49 { 1 }
		50 { 2 }
		51 { 3 }
		52 { 4 }
		53 { 5 }
		54 { 6 }
		55 { 7 }
		56 { 8 }
		57 { 9 }
		else { -1 }
	}
}

fn apply_float(op int, left f64, right f64) Result[f64] {
	return match op {
		1 {
			Result[f64]{
				val:   (left + right)
				is_ok: true
			}
		}
		2 {
			Result[f64]{
				val:   (left - right)
				is_ok: true
			}
		}
		3 {
			Result[f64]{
				val:   (left * right)
				is_ok: true
			}
		}
		4 {
			if right != 0.0 {
				Result[f64]{
					val:   (left / right)
					is_ok: true
				}
			} else {
				Result[f64]{
					err: 'Division by zero'
				}
			}
		}
		else {
			Result[f64]{
				val:   0.0
				is_ok: true
			}
		}
	}
}

fn precedence(op int) int {
	return match op {
		3 { 2 }
		4 { 2 }
		1 { 1 }
		2 { 1 }
		else { 0 }
	}
}

fn number_values(codes []int) []f64 {
	mut vals := []f64{}
	mut i := 0
	n := codes.len
	for i < n {
		code := codes[i]
		mut digit := digit_value(code)
		if digit >= 0 {
			mut value := 0.0
			for i < n {
				digit = digit_value(codes[i])
				if digit < 0 {
					break
				}
				value = ((value * 10.0) + f64(digit))
				i += 1
			}
			vals << value
		} else {
			i += 1
		}
	}
	return vals
}

fn tokenize(codes []int) []Token {
	mut toks := []Token{}
	mut i := 0
	n := codes.len
	mut prev_slash := false
	for i < n {
		code := codes[i]
		if code == 47 && prev_slash {
			i += 1
			continue
		}
		tok := match code {
			48 { Token(TokenNum{}) }
			49 { Token(TokenNum{}) }
			50 { Token(TokenNum{}) }
			51 { Token(TokenNum{}) }
			52 { Token(TokenNum{}) }
			53 { Token(TokenNum{}) }
			54 { Token(TokenNum{}) }
			55 { Token(TokenNum{}) }
			56 { Token(TokenNum{}) }
			57 { Token(TokenNum{}) }
			43 { Token(TokenPlus{}) }
			45 { Token(TokenMinus{}) }
			42 { Token(TokenStar{}) }
			47 { Token(TokenSlash{}) }
			40 { Token(TokenLparen{}) }
			41 { Token(TokenRparen{}) }
			else { Token(TokenSkip{}) }
		}

		prev_slash = if !(tok.is_skip()) { tok.is_slash() } else { prev_slash }
		toks << tok
		i += 1
	}
	return toks
}

fn lookup(env map[string]f64, name string) Result[f64] {
	if name in env {
		return Result[f64]{
			val:   env[name]
			is_ok: true
		}
	}
	return Result[f64]{
		err: 'undefined variable'
	}
}

fn combine(op int, l Result[f64], r Result[f64]) Result[f64] {
	if l.is_ok() {
		if r.is_ok() {
			return apply_float(op, l.unwrap_or(0.0), r.unwrap_or(0.0))
		}
		return r
	}
	return l
}

fn make_node(op int, left Expr, right Expr) Expr {
	return match op {
		1 { Expr(ExprAdd{
				left:  left
				right: right
			}) }
		2 { Expr(ExprSubtract{
				left:  left
				right: right
			}) }
		3 { Expr(ExprMultiply{
				left:  left
				right: right
			}) }
		4 { Expr(ExprDivide{
				left:  left
				right: right
			}) }
		else { Expr(0.0) }
	}
}

fn eval_expr(e Expr, env map[string]f64) Result[f64] {
	if e.is_number() {
		return Result[f64]{
			val:   e.number()
			is_ok: true
		}
	} else {
		if e.is_variable() {
			return lookup(env, e.variable())
		} else {
			if e.is_add() {
				b_add := e.add()
				return combine(plus, eval_expr(b_add.left, env), eval_expr(b_add.right, env))
			} else {
				if e.is_subtract() {
					b_subtract := e.subtract()
					return combine(minus, eval_expr(b_subtract.left, env), eval_expr(b_subtract.right,
						env))
				} else {
					if e.is_multiply() {
						b_multiply := e.multiply()
						return combine(star, eval_expr(b_multiply.left, env), eval_expr(b_multiply.right,
							env))
					} else {
						if e.is_divide() {
							b_divide := e.divide()
							return combine(slash, eval_expr(b_divide.left, env), eval_expr(b_divide.right,
								env))
						} else {
							return Result[f64]{
								err: 'unknown expression'
							}
						}
					}
				}
			}
		}
	}
}

fn parse(toks []Token, tvals []f64) []Expr {
	mut nodes := []Expr{}
	mut ops := []int{}
	mut nv := 0
	mut no := 0
	mut k := 0
	mut j := 0
	m := toks.len
	mut op := 0
	mut node := Expr(0.0)
	for j < m {
		if toks[j].is_skip() {
			j += 1
			continue
		}
		if toks[j].is_num() {
			for j < m {
				if !(toks[j].is_num()) {
					break
				}
				j += 1
			}
			if nv < nodes.len {
				nodes[nv] = Expr(tvals[k])
			} else {
				nodes << Expr(tvals[k])
			}
			k += 1
			nv += 1
			continue
		}
		if toks[j].is_lparen() {
			if no < ops.len {
				ops[no] = lparen
			} else {
				ops << lparen
			}
			no += 1
		} else {
			if toks[j].is_rparen() {
				for no > 0 {
					if ops[(no - 1)] == lparen {
						break
					}
					nv -= 2
					node = make_node(ops[(no - 1)], nodes[nv], nodes[(nv + 1)])
					if nv < nodes.len {
						nodes[nv] = node
					} else {
						nodes << node
					}
					nv += 1
					no -= 1
				}
				no -= 1
			} else {
				if toks[j].is_plus() {
					op = plus
				} else {
					if toks[j].is_minus() {
						op = minus
					} else {
						if toks[j].is_star() {
							op = star
						} else {
							op = slash
						}
					}
				}
				for no > 0 {
					if ops[(no - 1)] == lparen {
						break
					}
					if precedence(ops[(no - 1)]) < precedence(op) {
						break
					}
					nv -= 2
					node = make_node(ops[(no - 1)], nodes[nv], nodes[(nv + 1)])
					if nv < nodes.len {
						nodes[nv] = node
					} else {
						nodes << node
					}
					nv += 1
					no -= 1
				}
				if no < ops.len {
					ops[no] = op
				} else {
					ops << op
				}
				no += 1
			}
		}
		j += 1
	}
	for no > 0 {
		nv -= 2
		node = make_node(ops[(no - 1)], nodes[nv], nodes[(nv + 1)])
		if nv < nodes.len {
			nodes[nv] = node
		} else {
			nodes << node
		}
		nv += 1
		no -= 1
	}
	return nodes
}

fn evaluate(codes []int, env map[string]f64) Result[f64] {
	toks := tokenize(codes)
	tvals := number_values(codes)
	nodes := parse(toks, tvals)
	if nodes.len == 0 {
		return Result[f64]{
			err: 'empty expression'
		}
	}
	return eval_expr(nodes[0], env)
}

fn main() {
	env := {
		'x': 5.0
	}
	println((int(evaluate([50, 43, 51, 42, 52], env).unwrap_or(-999.0))).str())
	println((int(evaluate([40, 50, 43, 51, 41, 42, 52], env).unwrap_or(-999.0))).str())
	println((int(evaluate([49, 48, 45, 56, 47, 47, 50], env).unwrap_or(-999.0))).str())
	println((int(evaluate([55, 42, 56, 43, 57], env).unwrap_or(-999.0))).str())
	println((int(evaluate([40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54], env).unwrap_or(-999.0))).str())
	println((int(evaluate([49, 48, 47, 48], env).unwrap_or(-999.0))).str())
	println((int(eval_expr(Expr(ExprAdd{ left: Expr('x'), right: Expr(1.0) }), env).unwrap_or(-999.0))).str())
}
