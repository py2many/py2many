const std = @import("std");
const print = std.debug.print;
pub fn main_func() void {
    const a: i32 = std.math.pow(i32, 2, 4);
    print("{}\n", .{a});
}

pub fn main() void {
    main_func();
}
