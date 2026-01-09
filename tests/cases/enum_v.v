[translated]
module main


struct Colors {
    RED
    GREEN
    BLUE
}
struct Permissions {
    R = 1
    W = 2
    X = 16
}
struct StrEnum {
    ACTIVE string
    INACTIVE string
    PENDING string
}

const (
    ACTIVE: "active"
    INACTIVE: "inactive"
    PENDING: "pending"
)
fn show () {
  color := Colors.RED
  if color == Colors.RED {
    println('red')
}

  perm := (Permissions.R | Permissions.W)
  if (perm & Permissions.R) {
    println('has read')
}

  status := Status.ACTIVE
  if status == Status.ACTIVE {
    println('active')
}

  color_map := {Colors.RED: "red" Colors.GREEN: "green"}
  println((color_map.len).str())
}
fn main () {
  show()
}
