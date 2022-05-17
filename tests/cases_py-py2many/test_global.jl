#= Verify that warnings are issued for global statements following use. =#

using test.support.warnings_helper: check_warnings

import warnings
abstract type AbstractGlobalTests end
mutable struct GlobalTests <: AbstractGlobalTests
_warnings_manager
end
function setUp(self::GlobalTests)
self._warnings_manager = check_warnings()
__enter__(self._warnings_manager)
filterwarnings(warnings, "error", "<test string>")
end

function tearDown(self::GlobalTests)
__exit__(self._warnings_manager, nothing, nothing, nothing)
end

function test1(self::GlobalTests)
prog_text_1 = "def wrong1():\n    a = 1\n    b = 2\n    global a\n    global b\n"
check_syntax_error(self, prog_text_1, 4, 5)
end

function test2(self::GlobalTests)
prog_text_2 = "def wrong2():\n    print(x)\n    global x\n"
check_syntax_error(self, prog_text_2, 3, 5)
end

function test3(self::GlobalTests)
prog_text_3 = "def wrong3():\n    print(x)\n    x = 2\n    global x\n"
check_syntax_error(self, prog_text_3, 4, 5)
end

function test4(self::GlobalTests)
prog_text_4 = "global x\nx = 2\n"
compile(prog_text_4, "<test string>", "exec")
end

function setUpModule()
cm = catch_warnings(warnings)
__enter__(cm)
addModuleCleanup(unittest, cm.__exit__, nothing, nothing, nothing)
filterwarnings(warnings, "error", "<test string>")
end

function main()
global_tests = GlobalTests()
setUp(global_tests)
tearDown(global_tests)
test1(global_tests)
test2(global_tests)
test3(global_tests)
test4(global_tests)
end

main()