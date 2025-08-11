#!/bin/bash

# Create a zig project structure for tests
mkdir -p tests/build/common-zig-proj
cd tests/build/common-zig-proj

# Initialize zig project using zig init if build.zig doesn't exist
if [ ! -f build.zig ]; then
    echo "Initializing Zig project with zig init..."
    zig init
fi

# Add pylib-zig dependency
echo "Adding pylib-zig dependency..."
zig fetch --save https://github.com/adsharma/pylib-zig/archive/main.tar.gz

# Update build.zig to use pylib-zig dependency
echo "Configuring build.zig with pylib-zig..."
cat > build.zig << 'EOF'
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Add pylib-zig dependency
    const pylib_zig = b.dependency("pylib_zig", .{
        .target = target,
        .optimize = optimize,
    });

    // Create a module from the pylib-zig dependency
    const pylib_module = b.createModule(.{
        .root_source_file = pylib_zig.path("src/root.zig"),
    });

    // Create executable for running tests
    const exe = b.addExecutable(.{
        .name = "test",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Add the pylib module to our executable
    exe.root_module.addImport("pylib", pylib_module);
    b.installArtifact(exe);

    // Create run step
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_cmd.step);
}
EOF

# Create a simple placeholder main.zig file
mkdir -p src
echo "Creating placeholder main.zig..."
cat > src/main.zig << 'EOF'
const std = @import("std");
const print = std.debug.print;

pub fn main() void {
    print("Zig build environment ready!\n", .{});
    print("Use zig-runner.sh to run test files.\n", .{});
}
EOF

# Test the build to ensure everything is set up correctly
echo "Testing build setup..."
if zig build; then
    echo "Zig build environment setup successful!"
else
    echo "Build setup failed!"
    exit 1
fi

echo "Setup complete! Use zig-runner.sh to run individual test files."
