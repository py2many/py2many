[translated]
module main

fn show () {
  f := fn (x) { return (int(x) + 1) }
  println((f(5)).str())
  nums := [1, 2, 3]
  result := list(map(fn (x) { return (int(x) * 2) }, nums))
  println((result.len).str())
}
fn main () {
  show()
}
