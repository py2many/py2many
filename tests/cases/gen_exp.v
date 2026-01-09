[translated]
module main

fn show () {
  gen := 0..5.map((it * it))
  for val in gen {
    println((val).str())
}
}
fn main () {
  show()
}
