[translated]
module main

// Test cases for generator functions and yield statements

fn simple_generator (ch chan any) {
  ch <- 1
  ch <- 2
  ch <- 3
}
fn generator_with_type (ch chan any) {
  mut x := 0
  for x < 5 {
    ch <- x
    x += 1
}
}
fn generator_with_args (a int, b int, ch chan any) {
  for i in a..b {
    ch <- (int(i) * 2)
}
}
fn generator_with_yield_from (ch chan any) {
  fn inner (ch chan any) {
  ch <- 1
  ch <- 2
}
  // yield from spawn inner(, ch)
for val in spawn inner(, ch) {
    ch <- val
}
  ch <- 3
}
fn generator_with_condition (ch chan any) {
  for i in 0..10 {
    if (int(i) % 2) == 0 {
      ch <- i
}

}
}
fn test_generator_calls () {
  gen1 := spawn simple_generator(, ch)
  gen2 := spawn generator_with_args(1, 5, ch)
}
