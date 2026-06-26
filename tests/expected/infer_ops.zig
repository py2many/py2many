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

pub fn foo() void {
    const a: i32 = 10;
    const b: i32 = 20;
    _ = (a + b);
    _ = (a - b);
    _ = (a * b);
    _ = (a / b);
    _ = -(a);
    const d: f64 = 2.0;
    _ = (@as(f64, @floatFromInt(a)) + d);
    _ = (@as(f64, @floatFromInt(a)) - d);
    _ = (@as(f64, @floatFromInt(a)) * d);
    _ = (@as(f64, @floatFromInt(a)) / d);
    _ = -3.0;
    _ = -(a);
}

pub fn add1(x: i8, y: i8) i16 {
    return i16((x + y));
}

pub fn add2(x: i16, y: i16) i32 {
    return i32((x + y));
}

pub fn add3(x: i32, y: i32) i64 {
    return i64((x + y));
}

pub fn add4(x: i64, y: i64) i64 {
    return (x + y);
}

pub fn add5(x: u8, y: u8) u16 {
    return u16((x + y));
}

pub fn add6(x: u16, y: u16) u32 {
    return u32((x + y));
}

pub fn add7(x: u32, y: u32) u64 {
    return u64((x + y));
}

pub fn add8(x: u64, y: u64) u64 {
    return (x + y);
}

pub fn add9(x: i8, y: u16) u32 {
    return u32((@as(u16, @intCast(x)) + y));
}

pub fn sub(x: i8, y: i8) i8 {
    return (x - y);
}

pub fn mul(x: i8, y: i8) i16 {
    return i16((x * y));
}

pub fn fadd1(x: i8, y: f64) f64 {
    return (@as(f64, @floatFromInt(x)) + y);
}

pub fn show() !void {
    try expect(fadd1(6, 6.0) == 12);
    print("{s}\n", .{"OK"});
}

pub fn main() !void {
    foo();
    try show();
}
