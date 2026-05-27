const std = @import("std");
const expect = std.testing.expect;
const bar1 = @import("bar.zig").bar1;
const baz1 = @import("baz.zig").baz1;
pub fn main() !void {
    const x: i32 = bar1();
    const y: []const u8 = baz1();
    try expect(x == 0);
    try expect(y == "foo");
}
