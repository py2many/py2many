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

pub fn bubble_sort(seq: []i32) []i32 {
    const L = seq.len;
    for (0..L) |_| {
        for (1..L) |n| {
            if (seq[n] < seq[(n - 1)]) {
                {
                    const __tmp1 = seq[n];
                    const __tmp2 = seq[(n - 1)];
                    seq[(n - 1)] = __tmp1;
                    seq[n] = __tmp2;
                }
            }
        }
    }
    return seq;
}

pub fn main() !void {
    var unsorted = [_]i32{ 14, 11, 19, 5, 16, 10, 19, 12, 5, 12 };
    const expected = [_]i32{ 5, 5, 10, 11, 12, 12, 14, 16, 19, 19 };
    try expect(std.mem.eql(i32, bubble_sort(&unsorted), &expected));
    print("{s}\n", .{"OK"});
}
