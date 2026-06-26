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
pub fn default_builtins() !void {
    const a: []const u8 = "";
    const b: bool = false;
    const c: i32 = 0;
    const d: f64 = 0.0;
    try expect(std.mem.eql(u8, a, ""));
    try expect(b == false);
    try expect(c == 0);
    try expect(d == 0.0);
}

pub fn main() void {
    const a: i32 = @max(1, 2);
    print("{}\n", .{a});
    const b: i32 = @min(1, 2);
    print("{}\n", .{b});
    const c: i32 = @as(i32, @intFromFloat(@min(1.0, 2.0)));
    print("{}\n", .{c});
}
