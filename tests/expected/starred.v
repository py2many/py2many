[translated]
module main

fn show () {
  mut first, middle /* starred */, mut last := 1, 2, 3, 4, 5
  println((first).str() + ' ' + (last).str())
}
fn main () {
  show()
}
