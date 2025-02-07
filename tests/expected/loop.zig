const std = @import("std");
const print = std.debug.print;
pub fn for_with_break() void {
    for (0..4) |i| {
        if (i == 2) {
            break;
        }

        print("{}\n", .{i});
    }
}

pub fn for_with_continue() void {
    for (0..4) |i| {
        if (i == 2) {
            continue;
        }

        print("{}\n", .{i});
    }
}

pub fn for_with_else() void {
    const has_break: bool = false;
    for (0..4) |i| {
        print("{}\n", .{i});
    }
    if (has_break != true) {
        print("{s}\n", .{"OK"});
    }
}

pub fn while_with_break() void {
    var i: i32 = 0;
    while (true) {
        if (i == 2) {
            break;
        }

        print("{}\n", .{i});
        i += 1;
    }
}

pub fn while_with_continue() void {
    var i: i32 = 0;
    while (i < 5) {
        i += 1;
        if (i == 2) {
            continue;
        }

        print("{}\n", .{i});
    }
}

pub fn main() void {
    for_with_break();
    for_with_continue();
    for_with_else();
    while_with_break();
    while_with_continue();
}
