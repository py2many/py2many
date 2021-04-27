package main

import (
"fmt")




type Colors int

 const (
RED Colors = iota
GREEN = iota
BLUE = iota
)


type Permissions int

 const (
R Permissions = 1
W = 2
X = 16
)


func show() {
color_map := [(Colors.RED, "red"), (Colors.GREEN, "green"), (Colors.BLUE, "blue")].iter().cloned().collect::<HashMap<_,_>>()
a := Colors.GREEN
if(a == Colors.GREEN) {
fmt.Printf("%v\n","green")
} else {
fmt.Printf("%v\n","Not green")
}
b := Permissions.R
if(b == Permissions.R) {
fmt.Printf("%v\n","R")
} else {
fmt.Printf("%v\n","Not R")
}
if !(len(color_map) != 0) { panic("assert") }}


func main() {
show()}


