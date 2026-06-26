const std = @import("std");
const expect = std.testing.expect;

fn print(comptime fmt: []const u8, args: anytype) void {
    const io = std.Io.Threaded.global_single_threaded.io();
    var buffer: [1024]u8 = undefined;
    var writer = std.Io.File.stdout().writerStreaming(io, &buffer);
    const out = &writer.interface;
    out.print(fmt, args) catch return;
    out.flush() catch return;
}
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
