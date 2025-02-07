const std = @import("std");
const print = std.debug.print;
pub fn fib(i: i32) i32 {
    if (i == 0 or i == 1) {
        return 1;
    }

    return (fib((i - 1)) + fib((i - 2)));
}

pub fn main() void {
    print("{}\n", .{fib(5)});
}
