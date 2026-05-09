@[translated]
module main

import regex

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
	println((findall_res.len).str())
	sub_res := (fn (p string, r string, s string) string {
		mut re := regex.regex_opt(p) or { panic(err) }
		return re.replace(s, r)
	}('fox', 'cat', text))
	println(sub_res.str())
	split_res := (fn (p string, s string) []string {
		mut re := regex.regex_opt(p) or { panic(err) }
		return re.split(s)
	}('\\s+', text))
	println((split_res.len).str())
	pattern := regex.regex_opt('\\d+') or { panic(err) }
	println('Pattern compiled')
}

fn main() {
	test_re_methods()
}
