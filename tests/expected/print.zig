const std = @import("std");

fn print(comptime fmt: []const u8, args: anytype) void {
    const io = std.Io.Threaded.global_single_threaded.io();
    var buffer: [1024]u8 = undefined;
    var writer = std.Io.File.stdout().writerStreaming(io, &buffer);
    const out = &writer.interface;
    out.print(fmt, args) catch return;
    out.flush() catch return;
}
pub fn show() void {
    print("{s}\n", .{"b"});
    print("{} {s}\n", .{ 2, "b" });
    const a: f64 = 2.1;
    print("{}\n", .{a});
    const b: f64 = 2.1;
    print("{}\n", .{b});
    const c: bool = true;
    print("{s}\n", .{if (c) "True" else "False"});
}

pub fn main() void {
    show();
}
