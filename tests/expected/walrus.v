[translated]
module main

fn show () {
  if n := [1, 2, 3].len > 2 {
    println((n).str())
}

  mut i := 0
  for x := (i * 2) < 10 {
    println((x).str())
    i += 1
}
}
fn main () {
  show()
}
