#!/bin/bash

# Create a zig project structure for tests
mkdir -p tests/build
cd tests/build

# Initialize zig project if build.zig doesn't exist
if [ ! -f build.zig ]; then
    cat > build.zig << 'EOF'
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Add pylib-zig dependency
    const pylib_zig = b.dependency("pylib-zig", .{
        .target = target,
        .optimize = optimize,
    });

    // Create executable for running tests
    const exe = b.addExecutable(.{
        .name = "test",
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });

    exe.root_module.addImport("pylib", pylib_zig.module("pylib-zig"));
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
fi

# Initialize build.zig.zon if it doesn't exist
if [ ! -f build.zig.zon ]; then
    cat > build.zig.zon << 'EOF'
.{
    .name = "py2many-tests",
    .version = "0.0.1",
    .minimum_zig_version = "0.13.0",
    .dependencies = .{
        .@"pylib-zig" = .{
            .url = "https://github.com/adsharma/pylib-zig/archive/main.tar.gz",
            .hash = "12208e7c23456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef01",
        },
    },
    .paths = .{
        "build.zig",
        "build.zig.zon",
        "src",
    },
}
EOF
fi

# Create src directory
mkdir -p src

# Try to fetch the dependency to get the correct hash
echo "Fetching pylib-zig dependency..."
if ! zig build 2>/dev/null; then
    # If the hash is wrong, zig will tell us the correct one
    echo "Getting correct hash for pylib-zig..."
    zig build 2>&1 | grep "expected hash" | sed 's/.*expected hash //' | sed 's/,.*$//' > /tmp/correct_hash.txt
    if [ -s /tmp/correct_hash.txt ]; then
        CORRECT_HASH=$(cat /tmp/correct_hash.txt)
        echo "Updating build.zig.zon with correct hash: $CORRECT_HASH"
        sed -i "s/12208e7c.*/$CORRECT_HASH\",/" build.zig.zon
        # Try building again with correct hash
        zig build
    fi
fi

echo "Zig dependencies setup complete!"
