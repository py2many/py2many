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
// A ``tokenize`` lexer turns character codes into tokens with a large
// match that constructs one variant per arm, and ``evaluate`` dispatches
// on the token stream with ``is_*`` checks, e.g.::
//
//     tok = match code:
//         43: Token.PLUS()
//         47: Token.SLASH()
//         _: Token.SKIP()
//
//     for tok in toks:
//         if tok.is_skip():
//             continue
//         elif tok.is_rparen():
//             ...
//
// A ``/`` following another ``/`` is the second half of ``//``, not
// division: it is skipped before the match when the previous token was a
// slash. Numbers are lexed by a second pass (``number_values``) into a
// parallel list of values.
//
// Per the static-python rules, fallible functions return ``Result[V, E]``
// instead of raising: applying ``//`` to zero yields ``Err``, which the
// caller prints with ``unwrap_or``::
//
//     return match op:
//         4: Ok(left // right) if right != 0 else Error("Division by zero")
//         _: Ok(0)
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

fn apply_op(op int, left int, right int) Result[int] {
	return match op {
		1 {
			Result[int]{
				val:   (left + right)
				is_ok: true
			}
		}
		2 {
			Result[int]{
				val:   (left - right)
				is_ok: true
			}
		}
		3 {
			Result[int]{
				val:   (left * right)
				is_ok: true
			}
		}
		4 {
			if right != 0 {
				Result[int]{
					val:   (left / right)
					is_ok: true
				}
			} else {
				Result[int]{
					err: 'Division by zero'
				}
			}
		}
		else {
			Result[int]{
				val:   0
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

fn number_values(codes []int) []int {
	mut vals := []int{}
	mut i := 0
	n := codes.len
	for i < n {
		code := codes[i]
		mut digit := digit_value(code)
		if digit >= 0 {
			mut value := 0
			for i < n {
				digit = digit_value(codes[i])
				if digit < 0 {
					break
				}
				value = ((value * 10) + digit)
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

fn evaluate(codes []int) Result[int] {
	toks := tokenize(codes)
	tvals := number_values(codes)
	mut values := []int{}
	mut ops := []int{}
	mut nv := 0
	mut no := 0
	mut k := 0
	mut op := 0
	mut r := Result[int]{}
	mut j := 0
	m := toks.len
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
			if nv < values.len {
				values[nv] = tvals[k]
			} else {
				values << tvals[k]
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
					r = apply_op(ops[(no - 1)], values[nv], values[(nv + 1)])
					if r.is_ok() {
						values[nv] = r.unwrap_or(0)
						nv += 1
					} else {
						return r
					}
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
					r = apply_op(ops[(no - 1)], values[nv], values[(nv + 1)])
					if r.is_ok() {
						values[nv] = r.unwrap_or(0)
						nv += 1
					} else {
						return r
					}
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
		r = apply_op(ops[(no - 1)], values[nv], values[(nv + 1)])
		if r.is_ok() {
			values[nv] = r.unwrap_or(0)
			nv += 1
		} else {
			return r
		}
		no -= 1
	}
	if nv == 0 {
		return Result[int]{
			err: 'empty expression'
		}
	}
	return Result[int]{
		val:   values[0]
		is_ok: true
	}
}

fn main() {
	println((evaluate([50, 43, 51, 42, 52]).unwrap_or(-999)).str())
	println((evaluate([40, 50, 43, 51, 41, 42, 52]).unwrap_or(-999)).str())
	println((evaluate([49, 48, 45, 56, 47, 47, 50]).unwrap_or(-999)).str())
	println((evaluate([55, 42, 56, 43, 57]).unwrap_or(-999)).str())
	println((evaluate([40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54]).unwrap_or(-999)).str())
	println((evaluate([49, 48, 47, 48]).unwrap_or(-999)).str())
}
