const std = @import("std");

fn print(comptime fmt: []const u8, args: anytype) void {
    const io = std.Io.Threaded.global_single_threaded.io();
    var buffer: [1024]u8 = undefined;
    var writer = std.Io.File.stdout().writerStreaming(io, &buffer);
    const out = &writer.interface;
    out.print(fmt, args) catch return;
    out.flush() catch return;
}
pub fn fib(i: i32) i32 {
    if (i == 0 or i == 1) {
        return 1;
    }

    return (fib((i - 1)) + fib((i - 2)));
}

pub fn main() void {
    print("{}\n", .{fib(5)});
}
