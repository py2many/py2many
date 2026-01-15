@[translated]
module main

fn test_str_methods() {
	s := '  Hello World  '
	println((s.to_lower()).str())
	println((s.to_upper()).str())
	println((s.capitalize()).str())
	println((s.trim_space()).str())
	println((s.trim_left(' ')).str())
	println((s.trim_right(' ')).str())
	parts := s.fields()
	println(parts.str())
	joined := ['a', 'b', 'c'].join('-')
	println(joined.str())
	println((s.index('World') or { -1 }).str())
	println((s.replace('World', 'Vlang')).str())
	println(('123'.bytes().all(it.is_digit())).str())
	println(('abc'.bytes().all(it.is_letter())).str())
	println(('   '.trim_space() == '').str())
}

fn main() {
	test_str_methods()
}
