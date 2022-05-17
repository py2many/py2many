#= Test correct treatment of various string literals by the parser.

There are four types of string literals:

    'abc'             -- normal str
    r'abc'            -- raw str
    b'xyz'            -- normal bytes
    br'xyz' | rb'xyz' -- raw bytes

The difference between normal and raw strings is of course that in a
raw string, \ escapes (while still used to determine the end of the
literal) are not interpreted, so that r'\x00' contains four
characters: a backslash, an x, and two zeros; while '\x00' contains a
single character (code point zero).

The tricky thing is what should happen when non-ASCII bytes are used
inside literals.  For bytes literals, this is considered illegal.  But
for str literals, those bytes are supposed to be decoded using the
encoding declared for the file (UTF-8 by default).

We have to test this with various file encodings.  We also test it with
exec()/eval(), which uses a different code path.

This file is really about correct treatment of encodings and
backslashes.  It doesn't concern itself with issues like single
vs. double quotes or singly- vs. triply-quoted strings: that's dealt
with elsewhere (I assume).
 =#
using Test


import shutil
import tempfile

import warnings
abstract type AbstractTestLiterals end
TEMPLATE = "# coding: %s\na = \'x\'\nassert ord(a) == 120\nb = \'\\x01\'\nassert ord(b) == 1\nc = r\'\\x01\'\nassert list(map(ord, c)) == [92, 120, 48, 49]\nd = \'\\x81\'\nassert ord(d) == 0x81\ne = r\'\\x81\'\nassert list(map(ord, e)) == [92, 120, 56, 49]\nf = \'\\u1881\'\nassert ord(f) == 0x1881\ng = r\'\\u1881\'\nassert list(map(ord, g)) == [92, 117, 49, 56, 56, 49]\nh = \'\\U0001d120\'\nassert ord(h) == 0x1d120\ni = r\'\\U0001d120\'\nassert list(map(ord, i)) == [92, 85, 48, 48, 48, 49, 100, 49, 50, 48]\n"
function byte(i)::Array{UInt8}
return bytes([i])
end

mutable struct TestLiterals <: AbstractTestLiterals
save_path
tmpdir
check_encoding
end
function setUp(self::TestLiterals)
self.save_path = sys.path[begin:end]
self.tmpdir = mkdtemp(tempfile)
insert(sys.path, 0, self.tmpdir)
end

function tearDown(self::TestLiterals)
sys.path[begin:end] = self.save_path
rmtree(shutil, self.tmpdir, true)
end

function test_template(self::TestLiterals)
for c in TEMPLATE
@assert(c == "\n" || " " <= c <= "~")
end
end

function test_eval_str_normal(self::TestLiterals)
@test (eval(" \'x\' ") == "x")
@test (eval(" \'\\x01\' ") == chr(1))
@test (eval(" \'\' ") == chr(1))
@test (eval(" \'\\x81\' ") == chr(129))
@test (eval(" \'\' ") == chr(129))
@test (eval(" \'\\u1881\' ") == chr(6273))
@test (eval(" \'ᢁ\' ") == chr(6273))
@test (eval(" \'\\U0001d120\' ") == chr(119072))
@test (eval(" \'𝄠\' ") == chr(119072))
end

function test_eval_str_incomplete(self::TestLiterals)
@test_throws SyntaxError eval(" \'\\x\' ")
@test_throws SyntaxError eval(" \'\\x0\' ")
@test_throws SyntaxError eval(" \'\\u\' ")
@test_throws SyntaxError eval(" \'\\u0\' ")
@test_throws SyntaxError eval(" \'\\u00\' ")
@test_throws SyntaxError eval(" \'\\u000\' ")
@test_throws SyntaxError eval(" \'\\U\' ")
@test_throws SyntaxError eval(" \'\\U0\' ")
@test_throws SyntaxError eval(" \'\\U00\' ")
@test_throws SyntaxError eval(" \'\\U000\' ")
@test_throws SyntaxError eval(" \'\\U0000\' ")
@test_throws SyntaxError eval(" \'\\U00000\' ")
@test_throws SyntaxError eval(" \'\\U000000\' ")
@test_throws SyntaxError eval(" \'\\U0000000\' ")
end

function test_eval_str_invalid_escape(self::TestLiterals)
for b in 1:127
if b ∈ b"\n\r\"\'01234567NU\\abfnrtuvx"
continue;
end
assertWarns(self, DeprecationWarning) do 
@test (eval("\'\\%c\'" % b) == "\\" + chr(b))
end
end
catch_warnings(warnings, true) do w 
simplefilter(warnings, "always", DeprecationWarning)
eval("\'\'\'\n\\z\'\'\'")
end
@test (length(w) == 1)
@test (w[1].filename == "<string>")
@test (w[1].lineno == 1)
catch_warnings(warnings, true) do w 
simplefilter(warnings, "error", DeprecationWarning)
assertRaises(self, SyntaxError) do cm 
eval("\'\'\'\n\\z\'\'\'")
end
exc = cm.exception
end
@test (w == [])
@test (exc.filename == "<string>")
@test (exc.lineno == 1)
@test (exc.offset == 1)
end

function test_eval_str_raw(self::TestLiterals)
@test (eval(" r\'x\' ") == "x")
@test (eval(" r\'\\x01\' ") == "\\" * "x01")
@test (eval(" r\'\' ") == chr(1))
@test (eval(" r\'\\x81\' ") == "\\" * "x81")
@test (eval(" r\'\' ") == chr(129))
@test (eval(" r\'\\u1881\' ") == "\\" * "u1881")
@test (eval(" r\'ᢁ\' ") == chr(6273))
@test (eval(" r\'\\U0001d120\' ") == "\\" * "U0001d120")
@test (eval(" r\'𝄠\' ") == chr(119072))
end

function test_eval_bytes_normal(self::TestLiterals)
@test (eval(" b\'x\' ") == b"x")
@test (eval(" b\'\\x01\' ") == byte(1))
@test (eval(" b\'\' ") == byte(1))
@test (eval(" b\'\\x81\' ") == byte(129))
@test_throws SyntaxError eval(" b\'\' ")
@test (eval(" br\'\\u1881\' ") == append!(b"\\", b"u1881"))
@test_throws SyntaxError eval(" b\'ᢁ\' ")
@test (eval(" br\'\\U0001d120\' ") == append!(b"\\", b"U0001d120"))
@test_throws SyntaxError eval(" b\'𝄠\' ")
end

function test_eval_bytes_incomplete(self::TestLiterals)
@test_throws SyntaxError eval(" b\'\\x\' ")
@test_throws SyntaxError eval(" b\'\\x0\' ")
end

function test_eval_bytes_invalid_escape(self::TestLiterals)
for b in 1:127
if b ∈ b"\n\r\"\'01234567\\abfnrtvx"
continue;
end
assertWarns(self, DeprecationWarning) do 
@test (eval("b\'\\%c\'" % b) == append!(b"\\", bytes([b])))
end
end
catch_warnings(warnings, true) do w 
simplefilter(warnings, "always", DeprecationWarning)
eval("b\'\'\'\n\\z\'\'\'")
end
@test (length(w) == 1)
@test (w[1].filename == "<string>")
@test (w[1].lineno == 1)
catch_warnings(warnings, true) do w 
simplefilter(warnings, "error", DeprecationWarning)
assertRaises(self, SyntaxError) do cm 
eval("b\'\'\'\n\\z\'\'\'")
end
exc = cm.exception
end
@test (w == [])
@test (exc.filename == "<string>")
@test (exc.lineno == 1)
end

function test_eval_bytes_raw(self::TestLiterals)
@test (eval(" br\'x\' ") == b"x")
@test (eval(" rb\'x\' ") == b"x")
@test (eval(" br\'\\x01\' ") == append!(b"\\", b"x01"))
@test (eval(" rb\'\\x01\' ") == append!(b"\\", b"x01"))
@test (eval(" br\'\' ") == byte(1))
@test (eval(" rb\'\' ") == byte(1))
@test (eval(" br\'\\x81\' ") == append!(b"\\", b"x81"))
@test (eval(" rb\'\\x81\' ") == append!(b"\\", b"x81"))
@test_throws SyntaxError eval(" br\'\' ")
@test_throws SyntaxError eval(" rb\'\' ")
@test (eval(" br\'\\u1881\' ") == append!(b"\\", b"u1881"))
@test (eval(" rb\'\\u1881\' ") == append!(b"\\", b"u1881"))
@test_throws SyntaxError eval(" br\'ᢁ\' ")
@test_throws SyntaxError eval(" rb\'ᢁ\' ")
@test (eval(" br\'\\U0001d120\' ") == append!(b"\\", b"U0001d120"))
@test (eval(" rb\'\\U0001d120\' ") == append!(b"\\", b"U0001d120"))
@test_throws SyntaxError eval(" br\'𝄠\' ")
@test_throws SyntaxError eval(" rb\'𝄠\' ")
@test_throws SyntaxError eval(" bb\'\' ")
@test_throws SyntaxError eval(" rr\'\' ")
@test_throws SyntaxError eval(" brr\'\' ")
@test_throws SyntaxError eval(" bbr\'\' ")
@test_throws SyntaxError eval(" rrb\'\' ")
@test_throws SyntaxError eval(" rbb\'\' ")
end

function test_eval_str_u(self::TestLiterals)
@test (eval(" u\'x\' ") == "x")
@test (eval(" U\'ä\' ") == "ä")
@test (eval(" u\'ä\' ") == "ä")
@test_throws SyntaxError eval(" ur\'\' ")
@test_throws SyntaxError eval(" ru\'\' ")
@test_throws SyntaxError eval(" bu\'\' ")
@test_throws SyntaxError eval(" ub\'\' ")
end

function check_encoding(self::TestLiterals, encoding, extra = "")
modname = "xx_" + replace(encoding, "-", "_")
fn = join
f = readline(fn)
try
write(f, TEMPLATE % encoding)
write(f, extra)
finally
close(f)
end
__import__(modname)
#Delete Unsupported
del(sys.modules)
end

function test_file_utf_8(self::TestLiterals)
extra = "z = \'ሴ\'; assert ord(z) == 0x1234\n"
check_encoding(self, "utf-8", extra)
end

function test_file_utf_8_error(self::TestLiterals)
extra = "b\'\'\n"
@test_throws SyntaxError self.check_encoding("utf-8", extra)
end

function test_file_utf8(self::TestLiterals)
check_encoding(self, "utf-8")
end

function test_file_iso_8859_1(self::TestLiterals)
check_encoding(self, "iso-8859-1")
end

function test_file_latin_1(self::TestLiterals)
check_encoding(self, "latin-1")
end

function test_file_latin9(self::TestLiterals)
check_encoding(self, "latin9")
end

function main()
test_literals = TestLiterals()
setUp(test_literals)
tearDown(test_literals)
test_template(test_literals)
test_eval_str_normal(test_literals)
test_eval_str_incomplete(test_literals)
test_eval_str_invalid_escape(test_literals)
test_eval_str_raw(test_literals)
test_eval_bytes_normal(test_literals)
test_eval_bytes_incomplete(test_literals)
test_eval_bytes_invalid_escape(test_literals)
test_eval_bytes_raw(test_literals)
test_eval_str_u(test_literals)
check_encoding(test_literals)
test_file_utf_8(test_literals)
test_file_utf_8_error(test_literals)
test_file_utf8(test_literals)
test_file_iso_8859_1(test_literals)
test_file_latin_1(test_literals)
test_file_latin9(test_literals)
end

main()