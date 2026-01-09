[translated]
module main

fn simple_generator (ch chan any) {
  ch <- 1
  ch <- 2
  ch <- 3
}
fn show () {
  gen := spawn simple_generator(, ch)
  for val in gen {
    println((val).str())
}
}
fn main () {
  show()
}
