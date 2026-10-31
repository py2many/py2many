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
//         NUM: int = '0'
//         PLUS: int = '+'
//         ...
//
// and the parsed program is a recursive expression tree::
//
//     @sealed
//     class Expr:
//         NUMBER: float
//         VARIABLE: str
//         ADD(Expr, Expr)
//         ...
//
// A ``tokenize`` lexer turns character codes into tokens with a large
// match that constructs one variant per arm, a ``parse`` shunting-yard
// pass builds the tree, and a recursive ``eval_expr`` evaluates it by
// matching on variant with bindings, e.g.::
//
//     return match e:
//         Expr.NUMBER(n): Ok(n)
//         Expr.ADD(l, r): apply_float(Token.PLUS(), eval_expr(l, env), eval_expr(r, env))
//
// ``ops`` are ``Token``s themselves, not integer codes: there are no
// ``PLUS = 1`` style constants. ``precedence``, ``apply_float`` and
// ``make_node`` all take a ``Token`` and match on its variant::
//
//     return match op:
//         Token.PLUS(): Expr.ADD(left, right)
//         _: Expr.NUMBER(0.0)
//
// Character literals (``'+'``, ``')'``, ``'0'``) stand for their codes:
// no magic numbers appear. Token payloads default to their
// representative character, so constructions stay nullary
// (``Token.PLUS()`` means ``Token.PLUS('+')``).
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
//         Token.SLASH(): Ok(left / right) if right != 0.0 else Error("Division by zero")
//         _: Ok(0.0)
//
// The parser consumes a list of character codes (``[50, 43, 51]`` is
// ``"2+3"``), so the same source transpiles to Rust, V and CPython (whose
// ``match`` statement the python backend emits directly).

struct TokenNum {
	f0 int
}

struct TokenPlus {
	f0 int
}

struct TokenMinus {
	f0 int
}

struct TokenStar {
	f0 int
}

struct TokenSlash {
	f0 int
}

struct TokenLparen {
	f0 int
}

struct TokenRparen {
	f0 int
}

struct TokenSkip {
	f0 int
}

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

fn (t Token) num() TokenNum {
	if t is TokenNum {
		return t
	}
	panic('not a NUM')
}

fn (t Token) is_plus() bool {
	return t is TokenPlus
}

fn (t Token) plus() TokenPlus {
	if t is TokenPlus {
		return t
	}
	panic('not a PLUS')
}

fn (t Token) is_minus() bool {
	return t is TokenMinus
}

fn (t Token) minus() TokenMinus {
	if t is TokenMinus {
		return t
	}
	panic('not a MINUS')
}

fn (t Token) is_star() bool {
	return t is TokenStar
}

fn (t Token) star() TokenStar {
	if t is TokenStar {
		return t
	}
	panic('not a STAR')
}

fn (t Token) is_slash() bool {
	return t is TokenSlash
}

fn (t Token) slash() TokenSlash {
	if t is TokenSlash {
		return t
	}
	panic('not a SLASH')
}

fn (t Token) is_lparen() bool {
	return t is TokenLparen
}

fn (t Token) lparen() TokenLparen {
	if t is TokenLparen {
		return t
	}
	panic('not a LPAREN')
}

fn (t Token) is_rparen() bool {
	return t is TokenRparen
}

fn (t Token) rparen() TokenRparen {
	if t is TokenRparen {
		return t
	}
	panic('not a RPAREN')
}

fn (t Token) is_skip() bool {
	return t is TokenSkip
}

fn (t Token) skip() TokenSkip {
	if t is TokenSkip {
		return t
	}
	panic('not a SKIP')
}

struct ExprAdd {
	f0 Expr
	f1 Expr
}

struct ExprSubtract {
	f0 Expr
	f1 Expr
}

struct ExprMultiply {
	f0 Expr
	f1 Expr
}

struct ExprDivide {
	f0 Expr
	f1 Expr
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

fn apply_float(op Token, l Result[f64], r Result[f64]) Result[f64] {
	if l.is_ok() {
		if r.is_ok() {
			left := l.unwrap_or(0.0)
			right := r.unwrap_or(0.0)
			return match op {
				TokenPlus {
					Result[f64]{
						val:   (left + right)
						is_ok: true
					}
				}
				TokenMinus {
					Result[f64]{
						val:   (left - right)
						is_ok: true
					}
				}
				TokenStar {
					Result[f64]{
						val:   (left * right)
						is_ok: true
					}
				}
				TokenSlash {
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
		return r
	}
	return l
}

fn precedence(op Token) int {
	return match op {
		TokenStar { 2 }
		TokenSlash { 2 }
		TokenPlus { 1 }
		TokenMinus { 1 }
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
			48 { Token(TokenNum{
					f0: 48
				}) }
			49 { Token(TokenNum{
					f0: 48
				}) }
			50 { Token(TokenNum{
					f0: 48
				}) }
			51 { Token(TokenNum{
					f0: 48
				}) }
			52 { Token(TokenNum{
					f0: 48
				}) }
			53 { Token(TokenNum{
					f0: 48
				}) }
			54 { Token(TokenNum{
					f0: 48
				}) }
			55 { Token(TokenNum{
					f0: 48
				}) }
			56 { Token(TokenNum{
					f0: 48
				}) }
			57 { Token(TokenNum{
					f0: 48
				}) }
			43 { Token(TokenPlus{
					f0: 43
				}) }
			45 { Token(TokenMinus{
					f0: 45
				}) }
			42 { Token(TokenStar{
					f0: 42
				}) }
			47 { Token(TokenSlash{
					f0: 47
				}) }
			40 { Token(TokenLparen{
					f0: 40
				}) }
			41 { Token(TokenRparen{
					f0: 41
				}) }
			else { Token(TokenSkip{
					f0: 0
				}) }
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

fn make_node(op Token, left Expr, right Expr) Expr {
	return match op {
		TokenPlus { Expr(ExprAdd{
				f0: left
				f1: right
			}) }
		TokenMinus { Expr(ExprSubtract{
				f0: left
				f1: right
			}) }
		TokenStar { Expr(ExprMultiply{
				f0: left
				f1: right
			}) }
		TokenSlash { Expr(ExprDivide{
				f0: left
				f1: right
			}) }
		else { Expr(0.0) }
	}
}

fn eval_expr(e Expr, env map[string]f64) Result[f64] {
	return match e {
		f64 {
			Result[f64]{
				val:   f64(e)
				is_ok: true
			}
		}
		string {
			lookup(env, e.str())
		}
		ExprAdd {
			apply_float(Token(TokenPlus{ f0: 43 }), eval_expr(e.f0, env), eval_expr(e.f1, env))
		}
		ExprSubtract {
			apply_float(Token(TokenMinus{ f0: 45 }), eval_expr(e.f0, env), eval_expr(e.f1, env))
		}
		ExprMultiply {
			apply_float(Token(TokenStar{ f0: 42 }), eval_expr(e.f0, env), eval_expr(e.f1, env))
		}
		ExprDivide {
			apply_float(Token(TokenSlash{ f0: 47 }), eval_expr(e.f0, env), eval_expr(e.f1, env))
		}
		else {
			Result[f64]{
				err: 'unknown expression'
			}
		}
	}
}

fn parse(toks []Token, tvals []f64) []Expr {
	mut nodes := []Expr{}
	mut ops := []Token{}
	mut nv := 0
	mut no := 0
	mut k := 0
	mut j := 0
	m := toks.len
	mut op := Token(TokenNum{
		f0: 0
	})
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
				ops[no] = Token(TokenLparen{
					f0: 40
				})
			} else {
				ops << Token(TokenLparen{
					f0: 40
				})
			}
			no += 1
		} else {
			if toks[j].is_rparen() {
				for no > 0 {
					if ops[(no - 1)].is_lparen() {
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
				op = toks[j]
				for no > 0 {
					if ops[(no - 1)].is_lparen() {
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
	println((int(eval_expr(Expr(ExprAdd{ f0: Expr('x'), f1: Expr(1.0) }), env).unwrap_or(-999.0))).str())
}
