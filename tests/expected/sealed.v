@[translated]
module main

pub struct Packet {
pub mut:
	val f64
}

type Register = Packet | int

fn (r Register) is_packet() bool {
	return r is Packet
}

fn (r Register) packet() Packet {
	if r is Packet {
		return r
	}
	panic('not a PACKET')
}

fn (r Register) is_value() bool {
	return r is int
}

fn (r Register) value() int {
	if r is int {
		return r
	}
	panic('not a VALUE')
}

fn main() {
	a := Register(10)
	assert a.is_value()
	a.value()
	b := Register(Packet{
		val: 1.3
	})
	assert b.is_packet()
	b.packet()
	println('OK')
}
