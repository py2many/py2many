#= Test script for the binhex C module

   Uses the mechanism of the python binhex module
   Based on an original test by Roger E. Masse.
 =#
using Test





abstract type AbstractBinHexTestCase end
check_warnings(warnings_helper, ("", DeprecationWarning)) do 
binhex = import_fresh_module(import_helper, "binhex")
end
mutable struct BinHexTestCase <: AbstractBinHexTestCase
fname1
fname2
fname3
DATA::Array{UInt8}

                    BinHexTestCase(fname1, fname2, fname3, DATA::Array{UInt8} = b"Jack is my hero") =
                        new(fname1, fname2, fname3, DATA)
end
function setUp(self::BinHexTestCase)
self.fname1 = os_helper.TESTFN_ASCII + "1"
self.fname2 = os_helper.TESTFN_ASCII + "2"
self.fname3 = os_helper.TESTFN_ASCII + "very_long_filename__very_long_filename__very_long_filename__very_long_filename__"
end

function tearDown(self::BinHexTestCase)
unlink(os_helper, self.fname1)
unlink(os_helper, self.fname2)
unlink(os_helper, self.fname3)
end

function test_binhex(self::BinHexTestCase)
open(self.fname1, "wb") do f 
write(f, self.DATA)
end
binhex(binhex, self.fname1, self.fname2)
hexbin(binhex, self.fname2, self.fname1)
open(self.fname1, "rb") do f 
finish = readline(f)
end
@test (self.DATA == finish)
end

function test_binhex_error_on_long_filename(self::BinHexTestCase)
#= 
        The testcase fails if no exception is raised when a filename parameter provided to binhex.binhex()
        is too long, or if the exception raised in binhex.binhex() is not an instance of binhex.Error.
         =#
f3 = open(self.fname3, "wb")
close(f3)
@test_throws binhex.Error binhex.binhex(self.fname3, self.fname2)
end

function test_binhex_line_endings(self::BinHexTestCase)
open(self.fname1, "wb") do f 
write(f, self.DATA)
end
binhex(binhex, self.fname1, self.fname2)
open(self.fname2, "rb") do fp 
contents = read(fp)
end
assertNotIn(self, b"\n", contents)
end

function test_main()
run_unittest(support, BinHexTestCase)
end

function main()
test_main()
bin_hex_test_case = BinHexTestCase()
setUp(bin_hex_test_case)
tearDown(bin_hex_test_case)
test_binhex(bin_hex_test_case)
test_binhex_error_on_long_filename(bin_hex_test_case)
test_binhex_line_endings(bin_hex_test_case)
end

main()