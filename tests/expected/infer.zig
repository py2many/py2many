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
pub fn foo() !void {
    const a: i32 = 10;
    const b: i32 = a;
    try expect(b == 10);
    print("{}\n", .{b});
}

pub fn main() !void {
    try foo();
}
