#= test script for a few new invalid token catches =#
using Test





abstract type AbstractEOFTestCase end
mutable struct EOFTestCase <: AbstractEOFTestCase

end
function test_EOF_single_quote(self::EOFTestCase)
expect = "unterminated string literal (detected at line 1) (<string>, line 1)"
for quote_ in ("\'", "\"")
try
eval("$(quote_)this is a test                ")
catch exn
 let msg = exn
if msg isa SyntaxError
@test (string(msg) == expect)
@test (msg.offset == 1)
end
end
end
end
end

function test_EOFS(self::EOFTestCase)
expect = "unterminated triple-quoted string literal (detected at line 1) (<string>, line 1)"
try
eval("\'\'\'this is a test")
catch exn
 let msg = exn
if msg isa SyntaxError
@test (string(msg) == expect)
@test (msg.offset == 1)
end
end
end
end

function test_EOFS_with_file(self::EOFTestCase)
expect = "(<string>, line 1)"
temp_dir(os_helper) do temp_dir 
file_name = make_script(script_helper, temp_dir, "foo", "\'\'\'this is \na \ntest")
rc, out, err = assert_python_failure(script_helper, file_name)
end
assertIn(self, b"unterminated triple-quoted string literal (detected at line 3)", err)
end

function test_eof_with_line_continuation(self::EOFTestCase)
expect = "unexpected EOF while parsing (<string>, line 1)"
try
compile("\"\\xhh\" \\", "<string>", "exec", true)
catch exn
 let msg = exn
if msg isa SyntaxError
@test (string(msg) == expect)
end
end
end
end

function test_line_continuation_EOF(self::EOFTestCase)
#= A continuation at the end of input must be an error; bpo2180. =#
expect = "unexpected EOF while parsing (<string>, line 1)"
assertRaises(self, SyntaxError) do excinfo 
exec("x = 5\\")
end
@test (string(excinfo.exception) == expect)
assertRaises(self, SyntaxError) do excinfo 
exec("\\")
end
@test (string(excinfo.exception) == expect)
end

function test_line_continuation_EOF_from_file_bpo2180(self::EOFTestCase)
#= Ensure tok_nextc() does not add too many ending newlines. =#
temp_dir(os_helper) do temp_dir 
file_name = make_script(script_helper, temp_dir, "foo", "\\")
rc, out, err = assert_python_failure(script_helper, file_name)
assertIn(self, b"unexpected EOF while parsing", err)
assertIn(self, b"line 1", err)
assertIn(self, b"\\", err)
file_name = make_script(script_helper, temp_dir, "foo", "y = 6\\")
rc, out, err = assert_python_failure(script_helper, file_name)
assertIn(self, b"unexpected EOF while parsing", err)
assertIn(self, b"line 1", err)
assertIn(self, b"y = 6\\", err)
end
end

function main()
e_o_f_test_case = EOFTestCase()
test_EOF_single_quote(e_o_f_test_case)
test_EOFS(e_o_f_test_case)
test_EOFS_with_file(e_o_f_test_case)
test_eof_with_line_continuation(e_o_f_test_case)
test_line_continuation_EOF(e_o_f_test_case)
test_line_continuation_EOF_from_file_bpo2180(e_o_f_test_case)
end

main()