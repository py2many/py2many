@[translated]
module main

fn show() {
	my_list := [1, 2, 3, 4, 5]
	my_list.delete(2)
	println((my_list.len).str())
	my_dict := {
		'a': 1
		'b': 2
		'c': 3
	}
	my_dict.delete('b')
	println((my_dict.len).str())
}

fn main() {
	show()
}
