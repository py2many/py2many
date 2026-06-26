const std = @import("std");

fn print(comptime fmt: []const u8, args: anytype) void {
    const io = std.Io.Threaded.global_single_threaded.io();
    var buffer: [1024]u8 = undefined;
    var writer = std.Io.File.stdout().writerStreaming(io, &buffer);
    const out = &writer.interface;
    out.print(fmt, args) catch return;
    out.flush() catch return;
}
pub fn main() void {
    print("{s}\n", .{"Hello world!"});
    print("{s} {s}\n", .{ "Hello", "world!" });
}
