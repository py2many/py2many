[translated]
module main

pub struct MockFile {
pub mut:
name any
closed bool
}

fn (self MockFile) __init__ (name A) {
  self.name = name
  self.closed = false
}
fn (self MockFile) __enter__ () any {
  println(("".join(["Opening ", (self.name).str()])).str())
  return self
}
fn (self MockFile) __exit__ (exc_type A, exc_val B, exc_tb C) bool {
  println(("".join(["Closing ", (self.name).str()])).str())
  self.closed = true
  return false
}
fn (self MockFile) read () string {
  return "content"
}
fn show () {
  if true {
    f := MockFile{name: "test.txt"}
    println((f.read()).str())
}

}
fn main () {
  show()
}
