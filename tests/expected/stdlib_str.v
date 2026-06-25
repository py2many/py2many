@[translated]
module main

fn str_methods() {
	s := '  Hello World  '
	println((s.to_lower()).str())
	println((s.to_upper()).str())
	println((s.to_lower()).str())
	println((s.trim_space()).str())
	println((s.trim_left(' ')).str())
	println((s.trim_right(' ')).str())
	parts := s.fields()
	println(parts.str())
	joined := ['a', 'b', 'c'].join('-')
	println(joined.str())
	println((s.index('World') or { -1 }).str())
	println((s.replace('World', 'Vlang')).str())
	if '123'.bytes().all(it.is_digit()) {
		println('digit')
	}
	if 'abc'.bytes().all(it.is_letter()) {
		println('alpha')
	}
	if ('   '.trim_space() == '') {
		println('space')
	}
}

fn main() {
	str_methods()
}
