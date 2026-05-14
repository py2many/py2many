@[translated]
module main

fn implicit_keys() bool {
	codes := {
		'KEY': 1
	}
	return 'KEY' in codes
}

fn explicit_keys() bool {
	codes := {
		'KEY': 1
	}
	return 'KEY' in codes.keys()
}

fn dict_values() bool {
	codes := {
		'KEY': 1
	}
	return 1 in codes.keys().map(codes[it])
}

fn return_dict_index_str(key string) int {
	codes := {
		'KEY': 1
	}
	return codes[key]
}

fn return_dict_index_int(key int) string {
	codes := {
		1: 'one'
	}
	return codes[key]
}

fn main() {
	assert implicit_keys()
	assert explicit_keys()
	assert dict_values()
	assert return_dict_index_str('KEY') == 1
	assert return_dict_index_int(1) == 'one'
	println('OK')
}
