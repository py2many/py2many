@[translated]
module main

import regex

type AnyFn = fn (Any) Any

type Any = bool | int | i64 | f64 | string | []byte | voidptr
type List = []Any

fn any_to_string(value Any) string {
	return match value {
		string { value }
		bool, int, i64, f64 { value.str() }
		[]byte { value.bytestr() }
		voidptr { ptr_str(value) }
	}
}

fn test_re_methods() {
	text := 'The quick brown fox jumps over the lazy dog'
	search_res := (fn (p string, s string) bool {
		mut re := regex.regex_opt(p) or { panic(err) }
		return re.find_all_str(s).len > 0
	}('fox', text))
	if search_res {
		println('Found fox')
	}

	match_res := (fn (p string, s string) bool {
		mut re := regex.regex_opt('^' + p) or { panic(err) }
		return re.find_all_str(s).len > 0
	}('The', text))
	if match_res {
		println('Matched The')
	}

	findall_res := (fn (p string, s string) []string {
		mut re := regex.regex_opt(p) or { panic(err) }
		return re.find_all_str(s)
	}('\\w+', text))
	println(any_to_string(findall_res.len))
	sub_res := (fn (p string, r string, s string) string {
		mut re := regex.regex_opt(p) or { panic(err) }
		return re.replace(s, r)
	}('fox', 'cat', text))
	println(sub_res.str())
	split_res := (fn (p string, s string) []string {
		mut re := regex.regex_opt(p) or { panic(err) }
		return re.split(s)
	}('\\s+', text))
	println(any_to_string(split_res.len))
	pattern := regex.regex_opt('\\d+') or { panic(err) }
	println('Pattern compiled')
}

fn main() {
	test_re_methods()
}
