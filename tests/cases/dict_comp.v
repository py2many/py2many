[translated]
module main

fn show () {
  squares := mut result = map[any]any{}
for x in 0..5 {
        result[x] = (x * x)
}
result
  println((squares.len).str())
  evens := mut result = map[any]any{}
for x in 0..10 {
    if (int(x) % 2) == 0 {
        result[x] = (int(x) * 2)
    }
}
result
  println((evens.len).str())
}
fn main () {
  show()
}
