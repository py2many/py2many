package main

import (
	"bytes"
	"fmt"
)

func main() {
	if !(!bytes.Equal([]byte{0x66, 0x6f, 0x6f}, []byte{0x62, 0x61, 0x72})) {
		panic("assert")
	}
	if !(bytes.Equal([]byte{0x22}, []byte{0x22})) {
		panic("assert")
	}
	if !(bytes.Equal([]byte{0x27}, []byte{0x27})) {
		panic("assert")
	}
	if !(bytes.Equal([]byte{0xbb, 0x66, 0x6f, 0x6f}, []byte{0xbb, 0x66, 0x6f, 0x6f})) {
		panic("assert")
	}
	fmt.Printf("%v\n", "OK")
}
