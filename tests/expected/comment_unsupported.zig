const std = @import("std");

fn print(comptime fmt: []const u8, args: anytype) void {
    const io = std.Io.Threaded.global_single_threaded.io();
    var buffer: [1024]u8 = undefined;
    var writer = std.Io.File.stdout().writerStreaming(io, &buffer);
    const out = &writer.interface;
    out.print(fmt, args) catch return;
    out.flush() catch return;
}
pub fn do_unsupported() void {
    const a: i32 = 1;
    // dict comprehension ((key + 1), (value + 1)) unimplemented on line 9:4;
    const b: bool = (a != 0);
    print("{s}\n", .{if (b) "True" else "False"});
}

pub fn main() void {
    do_unsupported();
}
