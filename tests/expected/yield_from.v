[translated]
module main

fn generator1 (ch chan any) {
  ch <- 1
  ch <- 2
  ch <- 3
}
fn generator2 (ch chan any) {
  ch <- 0
  // yield from spawn generator1(, ch)
for val in spawn generator1(, ch) {
    ch <- val
}
  ch <- 4
}
fn show () {
  gen := spawn generator2(, ch)
  for val in gen {
    println((val).str())
}
}
fn main () {
  show()
}
