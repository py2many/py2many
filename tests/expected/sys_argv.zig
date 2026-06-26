const std = @import("std");
const expect = std.testing.expect;
const print = std.debug.print;

pub fn main(init: std.process.Init) !void {
    const arena = init.arena.allocator();
    const __raw = try init.minimal.args.toSlice(arena);
    const __argv = try arena.alloc([]const u8, __raw.len);
    __argv[0] = "sys_argv";
    for (__raw[1..], 1..) |__a, __i| __argv[__i] = __a;
    const a = __argv;
    const cmd: []const u8 = a[0];
    if (std.mem.eql(u8, cmd, "dart")) {} else {
        try expect((std.mem.indexOf(u8, cmd, "sys_argv") != null));
    }
    if (a.len > 1) {
        print("{s}\n", .{a[1]});
    } else {
        print("{s}\n", .{"OK"});
    }
}
