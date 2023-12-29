@[translated]
module main

fn implicit_keys() bool {
	CODES := {
		'KEY': 1
	}
	return 'KEY' in CODES
}

fn explicit_keys() bool {
	CODES := {
		'KEY': 1
	}
	return 'KEY' in CODES.keys()
}

fn dict_values() bool {
	CODES := {
		'KEY': 1
	}
	return 1 in CODES.keys().map(CODES[it])
}

fn return_dict_index_str(key string) int {
	CODES := {
		'KEY': 1
	}
	return CODES[key]
}

fn return_dict_index_int(key int) string {
	CODES := {
		1: 'one'
	}
	return CODES[key]
}

fn main() {
	assert implicit_keys()
	assert explicit_keys()
	assert dict_values()
	assert return_dict_index_str('KEY') == 1
	assert return_dict_index_int(1) == 'one'
	println('OK')
}
