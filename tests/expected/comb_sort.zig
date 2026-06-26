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

pub fn comb_sort(seq: []i32) []i32 {
    var gap = seq.len;
    var swap: bool = true;
    while (gap > 1 or swap) {
        gap = @max(1, @as(i32, @intFromFloat(@floor((@as(f64, @floatFromInt(gap)) / 1.25)))));
        swap = false;
        for (0..(seq.len - gap)) |i| {
            if (seq[i] > seq[(i + gap)]) {
                {
                    const __tmp1 = seq[(i + gap)];
                    const __tmp2 = seq[i];
                    seq[i] = __tmp1;
                    seq[(i + gap)] = __tmp2;
                }
                swap = true;
            }
        }
    }
    return seq;
}

pub fn main() !void {
    var unsorted = [_]i32{ 14, 11, 19, 5, 16, 10, 19, 12, 5, 12 };
    const expected = [_]i32{ 5, 5, 10, 11, 12, 12, 14, 16, 19, 19 };
    try expect(std.mem.eql(i32, comb_sort(&unsorted), &expected));
    print("{s}\n", .{"OK"});
}
