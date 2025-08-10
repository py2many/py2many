const std = @import("std");
const expect = std.testing.expect;
const print = std.debug.print;
pub fn compare_assert(a: i32, b: i32) !void {
    try expect(a == b);
    try expect(!(0 == 1));
}

pub fn main() !void {
    try expect(true);
    try expect(!(false));
    try compare_assert(1, 1);
    try expect(true);
    try expect(true);
    print("{s}\n", .{"OK"});
}
