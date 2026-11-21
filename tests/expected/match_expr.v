@[translated]
module main

// Tiny arithmetic expression parser and evaluator.
//
// Written in the match-as-expression dialect, shaped like a classic
// functional-language front end: a ``tokenize`` lexer turns character codes
// into token kinds with a large match, and ``evaluate`` parses and evaluates
// the token stream with an iterative shunting-yard evaluator, e.g.::
//
//     kind = match code:
//         48: NUM
//         43: PLUS
//         47: match prev:
//             4: SKIP
//             _: SLASH
//         _: -1
//
// A ``/`` following another ``/`` is the second half of ``//``, not
// division: the nested match spots it and marks it ``SKIP``.
//
// The parser consumes a list of character codes (``[50, 43, 51]`` is
// ``"2+3"``), so the same source transpiles to Rust, V and CPython (whose
// ``match`` statement the python backend emits directly).

const num = 0
const plus = 1
const minus = 2
const star = 3
const slash = 4
const lparen = 5
const rparen = 6
const skip = -2

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

fn tokenize(codes []int) []int {
	mut kinds := []int{}
	mut i := 0
	n := codes.len
	mut prev := 0
	for i < n {
		code := codes[i]
		kind := match code {
			48 {
				num
			}
			49 {
				num
			}
			50 {
				num
			}
			51 {
				num
			}
			52 {
				num
			}
			53 {
				num
			}
			54 {
				num
			}
			55 {
				num
			}
			56 {
				num
			}
			57 {
				num
			}
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
					4 { skip }
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

		kinds << kind
		if kind != skip {
			prev = kind
		}
		i += 1
	}
	return kinds
}

fn evaluate(codes []int) int {
	kinds := tokenize(codes)
	mut values := []int{}
	mut ops := []int{}
	mut nv := 0
	mut no := 0
	mut i := 0
	mut j := 0
	m := kinds.len
	for j < m {
		kind := kinds[j]
		if kind == skip {
			i += 1
			j += 1
			continue
		}
		if kind == num {
			mut value := 0
			for j < m {
				if kinds[j] != num {
					break
				}
				value = ((value * 10) + digit_value(codes[i]))
				i += 1
				j += 1
			}
			if nv < values.len {
				values[nv] = value
			} else {
				values << value
			}
			nv += 1
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
		i += 1
		j += 1
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
