@[translated]
module main

// Tiny arithmetic expression parser and evaluator.
//
// Written in the match-as-expression dialect: digit decoding, operator
// application and operator precedence are all match expressions, e.g.::
//
//     kind = match code:
//         43: PLUS
//         45: MINUS
//         _: -1
//
// The evaluator itself dispatches on the raw character code with a large
// match, as in a classic functional-language lexer. A ``/`` following
// another ``/`` is the second half of ``//``, not division: a nested
// match tells the two apart::
//
//     kind = match code:
//         47: match prev:
//             4: -2
//             _: SLASH
//         40: LPAREN
//         _: -1
//
// The parser consumes a list of character codes (``[50, 43, 51]`` is
// ``"2+3"``) with an iterative shunting-yard evaluator, so the same
// source transpiles to both Rust and CPython.

const plus = 1
const minus = 2
const star = 3
const slash = 4
const lparen = 5
const rparen = 6

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

fn apply_op(op int, left int, right int) int {
	return match op {
		1 { (left + right) }
		2 { (left - right) }
		3 { (left * right) }
		4 { (left / right) }
		else { 0 }
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

fn evaluate(codes []int) int {
	mut values := []int{}
	mut ops := []int{}
	mut nv := 0
	mut no := 0
	mut i := 0
	n := codes.len
	mut prev := 0
	for i < n {
		code := codes[i]
		kind := match code {
			43 {
				plus
			}
			45 {
				minus
			}
			42 {
				star
			}
			47 {
				match prev {
					4 { -2 }
					else { slash }
				}
			}
			40 {
				lparen
			}
			41 {
				rparen
			}
			else {
				-1
			}
		}

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
			if nv < values.len {
				values[nv] = value
			} else {
				values << value
			}
			nv += 1
			prev = -1
			continue
		}
		if kind == -2 {
			i += 1
			continue
		}
		if kind == lparen {
			if no < ops.len {
				ops[no] = kind
			} else {
				ops << kind
			}
			no += 1
		} else {
			if kind == rparen {
				for no > 0 {
					if ops[(no - 1)] == lparen {
						break
					}
					nv -= 2
					values[nv] = apply_op(ops[(no - 1)], values[nv], values[(nv + 1)])
					nv += 1
					no -= 1
				}
				no -= 1
			} else {
				for no > 0 {
					if ops[(no - 1)] == lparen {
						break
					}
					if precedence(ops[(no - 1)]) < precedence(kind) {
						break
					}
					nv -= 2
					values[nv] = apply_op(ops[(no - 1)], values[nv], values[(nv + 1)])
					nv += 1
					no -= 1
				}
				if no < ops.len {
					ops[no] = kind
				} else {
					ops << kind
				}
				no += 1
			}
		}
		prev = kind
		i += 1
	}
	for no > 0 {
		nv -= 2
		values[nv] = apply_op(ops[(no - 1)], values[nv], values[(nv + 1)])
		nv += 1
		no -= 1
	}
	return values[0]
}

fn main() {
	println((evaluate([50, 43, 51, 42, 52])).str())
	println((evaluate([40, 50, 43, 51, 41, 42, 52])).str())
	println((evaluate([49, 48, 45, 56, 47, 47, 50])).str())
	println((evaluate([55, 42, 56, 43, 57])).str())
	println((evaluate([40, 40, 50, 43, 51, 41, 42, 52, 41, 45, 54])).str())
}
