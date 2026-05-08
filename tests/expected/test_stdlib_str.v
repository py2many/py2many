@[translated]
module main

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

fn test_str_methods() {
	s := '  Hello World  '
	println(any_to_string(s.to_lower()))
	println(any_to_string(s.to_upper()))
	println(any_to_string(s.to_lower()))
	println(any_to_string(s.trim_space()))
	println(any_to_string(s.trim_left(' ')))
	println(any_to_string(s.trim_right(' ')))
	parts := s.fields()
	println(parts.str())
	joined := ['a', 'b', 'c'].join('-')
	println(joined.str())
	println(any_to_string((s.index('World') or { -1 })))
	println(any_to_string(s.replace('World', 'Vlang')))
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
	test_str_methods()
}
