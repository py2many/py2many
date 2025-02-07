const std = @import("std");
const print = std.debug.print;
pub fn main() void {
    print("{s}\n", .{"Hello world!"});
    print("{s} {s}\n", .{ "Hello", "world!" });
}
