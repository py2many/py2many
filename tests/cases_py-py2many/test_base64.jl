using Test
using io: BytesIO, StringIO







mutable struct LegacyBase64TestCase <: AbstractLegacyBase64TestCase

end
function check_type_errors(self::LegacyBase64TestCase, f)
@test_throws TypeError f("")
@test_throws TypeError f([])
multidimensional = cast(memoryview(b"1234"), "B", (2, 2))
@test_throws TypeError f(multidimensional)
int_data = cast(memoryview(b"1234"), "I")
@test_throws TypeError f(int_data)
end

function test_encodebytes(self::LegacyBase64TestCase)
eq = self.assertEqual
eq(encodebytes(base64, b"www.python.org"), b"d3d3LnB5dGhvbi5vcmc=\n")
eq(encodebytes(base64, b"a"), b"YQ==\n")
eq(encodebytes(base64, b"ab"), b"YWI=\n")
eq(encodebytes(base64, b"abc"), b"YWJj\n")
eq(encodebytes(base64, b""), b"")
eq(encodebytes(base64, b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}"), b"YWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXpBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWjAxMjM0\nNTY3ODkhQCMwXiYqKCk7Ojw+LC4gW117fQ==\n")
eq(encodebytes(base64, Vector{UInt8}(b"abc")), b"YWJj\n")
eq(encodebytes(base64, memoryview(b"abc")), b"YWJj\n")
eq(encodebytes(base64, array("B", b"abc")), b"YWJj\n")
check_type_errors(self, base64.encodebytes)
end

function test_decodebytes(self::LegacyBase64TestCase)
eq = self.assertEqual
eq(decodebytes(base64, b"d3d3LnB5dGhvbi5vcmc=\n"), b"www.python.org")
eq(decodebytes(base64, b"YQ==\n"), b"a")
eq(decodebytes(base64, b"YWI=\n"), b"ab")
eq(decodebytes(base64, b"YWJj\n"), b"abc")
eq(decodebytes(base64, b"YWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXpBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWjAxMjM0\nNTY3ODkhQCMwXiYqKCk7Ojw+LC4gW117fQ==\n"), b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}")
eq(decodebytes(base64, b""), b"")
eq(decodebytes(base64, Vector{UInt8}(b"YWJj\n")), b"abc")
eq(decodebytes(base64, memoryview(b"YWJj\n")), b"abc")
eq(decodebytes(base64, array("B", b"YWJj\n")), b"abc")
check_type_errors(self, base64.decodebytes)
end

function test_encode(self::LegacyBase64TestCase)
eq = self.assertEqual
infp = BytesIO(b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}")
outfp = BytesIO()
Vector{UInt8}(base64)
eq(getvalue(outfp), b"YWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXpBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWjAxMjM0\nNTY3ODkhQCMwXiYqKCk7Ojw+LC4gW117fQ==\n")
@test_throws TypeError Vector{UInt8}(base64)(StringIO("abc"), BytesIO())
@test_throws TypeError Vector{UInt8}(base64)(BytesIO(b"abc"), StringIO())
@test_throws TypeError Vector{UInt8}(base64)(StringIO("abc"), StringIO())
end

function test_decode(self::LegacyBase64TestCase)
infp = BytesIO(b"d3d3LnB5dGhvbi5vcmc=")
outfp = BytesIO()
decode(base64, infp, outfp)
@test (getvalue(outfp) == b"www.python.org")
@test_throws TypeError Vector{UInt8}(base64)(StringIO("YWJj\n"), BytesIO())
@test_throws TypeError Vector{UInt8}(base64)(BytesIO(b"YWJj\n"), StringIO())
@test_throws TypeError Vector{UInt8}(base64)(StringIO("YWJj\n"), StringIO())
end

abstract type AbstractLegacyBase64TestCase end
abstract type AbstractBaseXYTestCase end
abstract type AbstractTestMain end
mutable struct BaseXYTestCase <: AbstractBaseXYTestCase

end
function check_encode_type_errors(self::BaseXYTestCase, f)
@test_throws TypeError f("")
@test_throws TypeError f([])
end

function check_decode_type_errors(self::BaseXYTestCase, f)
@test_throws TypeError f([])
end

function check_other_types(self::BaseXYTestCase, f, bytes_data, expected)
eq = self.assertEqual
b = Vector{UInt8}(bytes_data)
eq(f(b), expected)
eq(b, bytes_data)
eq(f(memoryview(bytes_data)), expected)
eq(f(array("B", bytes_data)), expected)
check_nonbyte_element_format(self, base64.b64encode, bytes_data)
check_multidimensional(self, base64.b64encode, bytes_data)
end

function check_multidimensional(self::BaseXYTestCase, f, data)
padding = length(data) % 2 ? (b"\x00") : (b"")
bytes_data = data + padding
shape = (length(bytes_data) ÷ 2, 2)
multidimensional = cast(memoryview(bytes_data), "B", shape)
@test (f(multidimensional) == f(bytes_data))
end

function check_nonbyte_element_format(self::BaseXYTestCase, f, data)
padding = repeat(b"\x00",((4 - length(data)) % 4))
bytes_data = data + padding
int_data = cast(memoryview(bytes_data), "I")
@test (f(int_data) == f(bytes_data))
end

function test_b64encode(self::BaseXYTestCase)
eq = self.assertEqual
eq(b64encode(base64, b"www.python.org"), b"d3d3LnB5dGhvbi5vcmc=")
eq(b64encode(base64, b"\x00"), b"AA==")
eq(b64encode(base64, b"a"), b"YQ==")
eq(b64encode(base64, b"ab"), b"YWI=")
eq(b64encode(base64, b"abc"), b"YWJj")
eq(b64encode(base64, b""), b"")
eq(b64encode(base64, b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}"), b"YWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXpBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWjAxMjM0NTY3ODkhQCMwXiYqKCk7Ojw+LC4gW117fQ==")
eq(b64encode(base64, b"\xd3V\xbeo\xf7\x1d", b"*$"), b"01a*b$cd")
eq(b64encode(base64, b"\xd3V\xbeo\xf7\x1d", Vector{UInt8}(b"*$")), b"01a*b$cd")
eq(b64encode(base64, b"\xd3V\xbeo\xf7\x1d", memoryview(b"*$")), b"01a*b$cd")
eq(b64encode(base64, b"\xd3V\xbeo\xf7\x1d", array("B", b"*$")), b"01a*b$cd")
check_other_types(self, base64.b64encode, b"abcd", b"YWJjZA==")
check_encode_type_errors(self, base64.b64encode)
@test_throws TypeError base64.b64encode(b"", "*\$")
eq(standard_b64encode(base64, b"www.python.org"), b"d3d3LnB5dGhvbi5vcmc=")
eq(standard_b64encode(base64, b"a"), b"YQ==")
eq(standard_b64encode(base64, b"ab"), b"YWI=")
eq(standard_b64encode(base64, b"abc"), b"YWJj")
eq(standard_b64encode(base64, b""), b"")
eq(standard_b64encode(base64, b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}"), b"YWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXpBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWjAxMjM0NTY3ODkhQCMwXiYqKCk7Ojw+LC4gW117fQ==")
check_other_types(self, base64.standard_b64encode, b"abcd", b"YWJjZA==")
check_encode_type_errors(self, base64.standard_b64encode)
eq(urlsafe_b64encode(base64, b"\xd3V\xbeo\xf7\x1d"), b"01a-b_cd")
check_other_types(self, base64.urlsafe_b64encode, b"\xd3V\xbeo\xf7\x1d", b"01a-b_cd")
check_encode_type_errors(self, base64.urlsafe_b64encode)
end

function test_b64decode(self::BaseXYTestCase)
eq = self.assertEqual
tests = Dict(b"d3d3LnB5dGhvbi5vcmc=" => b"www.python.org", b"AA==" => b"\x00", b"YQ==" => b"a", b"YWI=" => b"ab", b"YWJj" => b"abc", b"YWJjZGVmZ2hpamtsbW5vcHFyc3R1dnd4eXpBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWjAxMjM0\nNTY3ODkhQCMwXiYqKCk7Ojw+LC4gW117fQ==" => b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}", b"" => b"")
for (data, res) in items(tests)
eq(b64decode(base64, data), res)
eq(b64decode(base64, decode(data, "ascii")), res)
end
check_other_types(self, base64.b64decode, b"YWJj", b"abc")
check_decode_type_errors(self, base64.b64decode)
tests_altchars = Dict((b"01a*b$cd", b"*$") => b"\xd3V\xbeo\xf7\x1d")
for ((data, altchars), res) in items(tests_altchars)
data_str = decode(data, "ascii")
altchars_str = decode(altchars, "ascii")
eq(b64decode(base64, data, altchars), res)
eq(b64decode(base64, data_str, altchars), res)
eq(b64decode(base64, data, altchars_str), res)
eq(b64decode(base64, data_str, altchars_str), res)
end
for (data, res) in items(tests)
eq(standard_b64decode(base64, data), res)
eq(standard_b64decode(base64, decode(data, "ascii")), res)
end
check_other_types(self, base64.standard_b64decode, b"YWJj", b"abc")
check_decode_type_errors(self, base64.standard_b64decode)
tests_urlsafe = Dict(b"01a-b_cd" => b"\xd3V\xbeo\xf7\x1d", b"" => b"")
for (data, res) in items(tests_urlsafe)
eq(urlsafe_b64decode(base64, data), res)
eq(urlsafe_b64decode(base64, decode(data, "ascii")), res)
end
check_other_types(self, base64.urlsafe_b64decode, b"01a-b_cd", b"\xd3V\xbeo\xf7\x1d")
check_decode_type_errors(self, base64.urlsafe_b64decode)
end

function test_b64decode_padding_error(self::BaseXYTestCase)
@test_throws binascii.Error base64.b64decode(b"abc")
@test_throws binascii.Error base64.b64decode("abc")
end

function test_b64decode_invalid_chars(self::BaseXYTestCase)
tests = ((b"%3d==", b"\xdd"), (b"$3d==", b"\xdd"), (b"[==", b""), (b"YW]3=", b"am"), (b"3{d==", b"\xdd"), (b"3d}==", b"\xdd"), (b"@@", b""), (b"!", b""), (b"YWJj\n", b"abc"), (b"YWJj\nYWI=", b"abcab"))
funcs = (base64.b64decode, base64.standard_b64decode, base64.urlsafe_b64decode)
for (bstr, res) in tests
for func in funcs
subTest(self, bstr, func) do 
@test (func(bstr) == res)
@test (func(decode(bstr, "ascii")) == res)
end
end
assertRaises(self, binascii.Error) do 
b64decode(base64, bstr, true)
end
assertRaises(self, binascii.Error) do 
b64decode(base64, decode(bstr, "ascii"), true)
end
end
res = b"\xfb\xef\xbe\xff\xff\xff"
@test (b64decode(base64, b"++[[//]]", b"[]") == res)
@test (urlsafe_b64decode(base64, b"++--//__") == res)
end

function test_b32encode(self::BaseXYTestCase)
eq = self.assertEqual
eq(b32encode(base64, b""), b"")
eq(b32encode(base64, b"\x00"), b"AA======")
eq(b32encode(base64, b"a"), b"ME======")
eq(b32encode(base64, b"ab"), b"MFRA====")
eq(b32encode(base64, b"abc"), b"MFRGG===")
eq(b32encode(base64, b"abcd"), b"MFRGGZA=")
eq(b32encode(base64, b"abcde"), b"MFRGGZDF")
check_other_types(self, base64.b32encode, b"abcd", b"MFRGGZA=")
check_encode_type_errors(self, base64.b32encode)
end

function test_b32decode(self::BaseXYTestCase)
eq = self.assertEqual
tests = Dict(b"" => b"", b"AA======" => b"\x00", b"ME======" => b"a", b"MFRA====" => b"ab", b"MFRGG===" => b"abc", b"MFRGGZA=" => b"abcd", b"MFRGGZDF" => b"abcde")
for (data, res) in items(tests)
eq(b32decode(base64, data), res)
eq(b32decode(base64, decode(data, "ascii")), res)
end
check_other_types(self, base64.b32decode, b"MFRGG===", b"abc")
check_decode_type_errors(self, base64.b32decode)
end

function test_b32decode_casefold(self::BaseXYTestCase)
eq = self.assertEqual
tests = Dict(b"" => b"", b"ME======" => b"a", b"MFRA====" => b"ab", b"MFRGG===" => b"abc", b"MFRGGZA=" => b"abcd", b"MFRGGZDF" => b"abcde", b"me======" => b"a", b"mfra====" => b"ab", b"mfrgg===" => b"abc", b"mfrggza=" => b"abcd", b"mfrggzdf" => b"abcde")
for (data, res) in items(tests)
eq(b32decode(base64, data, true), res)
eq(b32decode(base64, decode(data, "ascii"), true), res)
end
@test_throws binascii.Error base64.b32decode(b"me======")
@test_throws binascii.Error base64.b32decode("me======")
eq(b32decode(base64, b"MLO23456"), b"b\xdd\xad\xf3\xbe")
eq(b32decode(base64, "MLO23456"), b"b\xdd\xad\xf3\xbe")
map_tests = Dict((b"M1023456", b"L") => b"b\xdd\xad\xf3\xbe", (b"M1023456", b"I") => b"b\x1d\xad\xf3\xbe")
for ((data, map01), res) in items(map_tests)
data_str = decode(data, "ascii")
map01_str = decode(map01, "ascii")
eq(b32decode(base64, data, map01), res)
eq(b32decode(base64, data_str, map01), res)
eq(b32decode(base64, data, map01_str), res)
eq(b32decode(base64, data_str, map01_str), res)
@test_throws binascii.Error base64.b32decode(data)
@test_throws binascii.Error base64.b32decode(data_str)
end
end

function test_b32decode_error(self::BaseXYTestCase)
tests = [b"abc", b"ABCDEF==", b"==ABCDEF"]
prefixes = [b"M", b"ME", b"MFRA", b"MFRGG", b"MFRGGZA", b"MFRGGZDF"]
for i in 0:16
if i
push!(tests, b"="*i)
end
for prefix in prefixes
if (length(prefix) + i) != 8
push!(tests, append!(prefix, b"="*i))
end
end
end
for data in tests
subTest(self, data) do 
assertRaises(self, binascii.Error) do 
b32decode(base64, data)
end
assertRaises(self, binascii.Error) do 
b32decode(base64, decode(data, "ascii"))
end
end
end
end

function test_b32hexencode(self::BaseXYTestCase)
test_cases = [(b"", b""), (b"\x00", b"00======"), (b"a", b"C4======"), (b"ab", b"C5H0===="), (b"abc", b"C5H66==="), (b"abcd", b"C5H66P0="), (b"abcde", b"C5H66P35")]
for (to_encode, expected) in test_cases
subTest(self, to_encode) do 
@test (b32hexencode(base64, to_encode) == expected)
end
end
end

function test_b32hexencode_other_types(self::BaseXYTestCase)
check_other_types(self, base64.b32hexencode, b"abcd", b"C5H66P0=")
check_encode_type_errors(self, base64.b32hexencode)
end

function test_b32hexdecode(self::BaseXYTestCase)
test_cases = [(b"", b"", false), (b"00======", b"\x00", false), (b"C4======", b"a", false), (b"C5H0====", b"ab", false), (b"C5H66===", b"abc", false), (b"C5H66P0=", b"abcd", false), (b"C5H66P35", b"abcde", false), (b"", b"", true), (b"00======", b"\x00", true), (b"C4======", b"a", true), (b"C5H0====", b"ab", true), (b"C5H66===", b"abc", true), (b"C5H66P0=", b"abcd", true), (b"C5H66P35", b"abcde", true), (b"c4======", b"a", true), (b"c5h0====", b"ab", true), (b"c5h66===", b"abc", true), (b"c5h66p0=", b"abcd", true), (b"c5h66p35", b"abcde", true)]
for (to_decode, expected, casefold) in test_cases
subTest(self, to_decode, casefold) do 
@test (b32hexdecode(base64, to_decode, casefold) == expected)
@test (b32hexdecode(base64, decode(to_decode, "ascii"), casefold) == expected)
end
end
end

function test_b32hexdecode_other_types(self::BaseXYTestCase)
check_other_types(self, base64.b32hexdecode, b"C5H66===", b"abc")
check_decode_type_errors(self, base64.b32hexdecode)
end

function test_b32hexdecode_error(self::BaseXYTestCase)
tests = [b"abc", b"ABCDEF==", b"==ABCDEF", b"c4======"]
prefixes = [b"M", b"ME", b"MFRA", b"MFRGG", b"MFRGGZA", b"MFRGGZDF"]
for i in 0:16
if i
push!(tests, b"="*i)
end
for prefix in prefixes
if (length(prefix) + i) != 8
push!(tests, append!(prefix, b"="*i))
end
end
end
for data in tests
subTest(self, data) do 
assertRaises(self, binascii.Error) do 
b32hexdecode(base64, data)
end
assertRaises(self, binascii.Error) do 
b32hexdecode(base64, decode(data, "ascii"))
end
end
end
end

function test_b16encode(self::BaseXYTestCase)
eq = self.assertEqual
eq(b16encode(base64, b"\x01\x02\xab\xcd\xef"), b"0102ABCDEF")
eq(b16encode(base64, b"\x00"), b"00")
check_other_types(self, base64.b16encode, b"\x01\x02\xab\xcd\xef", b"0102ABCDEF")
check_encode_type_errors(self, base64.b16encode)
end

function test_b16decode(self::BaseXYTestCase)
eq = self.assertEqual
eq(b16decode(base64, b"0102ABCDEF"), b"\x01\x02\xab\xcd\xef")
eq(b16decode(base64, "0102ABCDEF"), b"\x01\x02\xab\xcd\xef")
eq(b16decode(base64, b"00"), b"\x00")
eq(b16decode(base64, "00"), b"\x00")
@test_throws binascii.Error base64.b16decode(b"0102abcdef")
@test_throws binascii.Error base64.b16decode("0102abcdef")
eq(b16decode(base64, b"0102abcdef", true), b"\x01\x02\xab\xcd\xef")
eq(b16decode(base64, "0102abcdef", true), b"\x01\x02\xab\xcd\xef")
check_other_types(self, base64.b16decode, b"0102ABCDEF", b"\x01\x02\xab\xcd\xef")
check_decode_type_errors(self, base64.b16decode)
eq(b16decode(base64, Vector{UInt8}(b"0102abcdef"), true), b"\x01\x02\xab\xcd\xef")
eq(b16decode(base64, memoryview(b"0102abcdef"), true), b"\x01\x02\xab\xcd\xef")
eq(b16decode(base64, array("B", b"0102abcdef"), true), b"\x01\x02\xab\xcd\xef")
@test_throws binascii.Error base64.b16decode("0102AG")
@test_throws binascii.Error base64.b16decode("010")
end

function test_a85encode(self::BaseXYTestCase)
eq = self.assertEqual
tests = Dict(b"" => b"", b"www.python.org" => b"GB\\6`E-ZP=Df.1GEb>", bytes(0:254) => b"!!*-\'\"9eu7#RLhG$k3[W&.oNg\'GVB\"(`=52*$$(B+<_pR,UFcb-n-Vr/1iJ-0JP==1c70M3&s#]4?Ykm5X@_(6q\'R884cEH9MJ8X:f1+h<)lt#=BSg3>[:ZC?t!MSA7]@cBPD3sCi+\'.E,fo>FEMbNG^4U^I!pHnJ:W<)KS>/9Ll%\"IN/`jYOHG]iPa.Q$R$jD4S=Q7DTV8*TUnsrdW2ZetXKAY/Yd(L?[\'d?O\\@K2_]Y2%o^qmn*`5Ta:aN;TJbg\"GZd*^:jeCE.%f\\,!5gtgiEi8N\\UjQ5OekiqBum-X60nF?)@o_%qPq\"ad`r;HT", b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}" => b"@:E_WAS,RgBkhF\"D/O92EH6,BF`qtRH$VbC6UX@47n?3D92&&T:Jand;cHat=\'/U/0JP==1c70M3&r-I,;<FN.OZ`-3]oSW/g+A(H[P", b"no padding.." => b"DJpY:@:Wn_DJ(RS", b"zero compression\x00\x00\x00\x00" => b"H=_,8+Cf>,E,oN2F(oQ1z", b"zero compression\x00\x00\x00" => b"H=_,8+Cf>,E,oN2F(oQ1!!!!", b"Boundary:\x00\x00\x00\x00" => b"6>q!aA79M(3WK-[!!", b"Space compr:    " => b";fH/TAKYK$D/aMV+<VdL", b"\xff" => b"rr", repeat(b"\xff",2) => b"s8N", repeat(b"\xff",3) => b"s8W*", repeat(b"\xff",4) => b"s8W-!")
for (data, res) in items(tests)
eq(a85encode(base64, data), res, data)
eq(a85encode(base64, data, false), res, data)
eq(a85encode(base64, data, true), append!((b"<~" + res), b"~>"), data)
end
check_other_types(self, base64.a85encode, b"www.python.org", b"GB\\6`E-ZP=Df.1GEb>")
@test_throws TypeError base64.a85encode("")
eq(a85encode(base64, b"www.python.org", 7, false), b"GB\\6`E-\nZP=Df.1\nGEb>")
eq(a85encode(base64, b"\x00\x00\x00\x00www.python.org", 7, false), b"zGB\\6`E\n-ZP=Df.\n1GEb>")
eq(a85encode(base64, b"www.python.org", 7, true), b"<~GB\\6`\nE-ZP=Df\n.1GEb>\n~>")
eq(a85encode(base64, repeat(b" ",8), true, false), b"yy")
eq(a85encode(base64, repeat(b" ",7), true, false), b"y+<Vd")
eq(a85encode(base64, repeat(b" ",6), true, false), b"y+<U")
eq(a85encode(base64, repeat(b" ",5), true, false), b"y+9")
end

function test_b85encode(self::BaseXYTestCase)
eq = self.assertEqual
tests = Dict(b"" => b"", b"www.python.org" => b"cXxL#aCvlSZ*DGca%T", bytes(0:254) => b"009C61O)~M2nh-c3=Iws5D^j+6crX17#SKH9337XAR!_nBqb&%C@Cr{EG;fCFflSSG&MFiI5|2yJUu=?KtV!7L`6nNNJ&adOifNtP*GA-R8>}2SXo+ITwPvYU}0ioWMyV&XlZI|Y;A6DaB*^Tbai%jczJqze0_d@fPsR8goTEOh>41ejE#<ukdcy;l$Dm3n3<ZJoSmMZprN9pq@|{(sHv)}tgWuEu(7hUw6(UkxVgH!yuH4^z`?@9#Kp$P$jQpf%+1cv(9zP<)YaD4*xB0K+}+;a;Njxq<mKk)=;`X~?CtLF@bU8V^!4`l`1$(#{Qdp", b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}" => b"VPa!sWoBn+X=-b1ZEkOHadLBXb#`}nd3r%YLqtVJM@UIZOH55pPf$@(Q&d$}S6EqEFflSSG&MFiI5{CeBQRbjDkv#CIy^osE+AW7dwl", b"no padding.." => b"Zf_uPVPs@!Zf7no", b"zero compression\x00\x00\x00\x00" => b"dS!BNAY*TBaB^jHb7^mG00000", b"zero compression\x00\x00\x00" => b"dS!BNAY*TBaB^jHb7^mG0000", b"Boundary:\x00\x00\x00\x00" => b"LT`0$WMOi7IsgCw00", b"Space compr:    " => b"Q*dEpWgug3ZE$irARr(h", b"\xff" => b"{{", repeat(b"\xff",2) => b"|Nj", repeat(b"\xff",3) => b"|Ns9", repeat(b"\xff",4) => b"|NsC0")
for (data, res) in items(tests)
eq(b85encode(base64, data), res)
end
check_other_types(self, base64.b85encode, b"www.python.org", b"cXxL#aCvlSZ*DGca%T")
end

function test_a85decode(self::BaseXYTestCase)
eq = self.assertEqual
tests = Dict(b"" => b"", b"GB\\6`E-ZP=Df.1GEb>" => b"www.python.org", b"! ! * -\'\"\n\t\t9eu\r\n7#  RL\x0bhG$k3[W&.oNg\'GVB\"(`=52*$$(B+<_pR,UFcb-n-Vr/1iJ-0JP==1c70M3&s#]4?Ykm5X@_(6q\'R884cEH9MJ8X:f1+h<)lt#=BSg3>[:ZC?t!MSA7]@cBPD3sCi+\'.E,fo>FEMbNG^4U^I!pHnJ:W<)KS>/9Ll%\"IN/`jYOHG]iPa.Q$R$jD4S=Q7DTV8*TUnsrdW2ZetXKAY/Yd(L?[\'d?O\\@K2_]Y2%o^qmn*`5Ta:aN;TJbg\"GZd*^:jeCE.%f\\,!5gtgiEi8N\\UjQ5OekiqBum-X60nF?)@o_%qPq\"ad`r;HT" => bytes(0:254), b"@:E_WAS,RgBkhF\"D/O92EH6,BF`qtRH$VbC6UX@47n?3D92&&T:Jand;cHat=\'/U/0JP==1c70M3&r-I,;<FN.OZ`-3]oSW/g+A(H[P" => b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}", b"DJpY:@:Wn_DJ(RS" => b"no padding..", b"H=_,8+Cf>,E,oN2F(oQ1z" => b"zero compression\x00\x00\x00\x00", b"H=_,8+Cf>,E,oN2F(oQ1!!!!" => b"zero compression\x00\x00\x00", b"6>q!aA79M(3WK-[!!" => b"Boundary:\x00\x00\x00\x00", b";fH/TAKYK$D/aMV+<VdL" => b"Space compr:    ", b"rr" => b"\xff", b"s8N" => repeat(b"\xff",2), b"s8W*" => repeat(b"\xff",3), b"s8W-!" => repeat(b"\xff",4))
for (data, res) in items(tests)
eq(a85decode(base64, data), res, data)
eq(a85decode(base64, data, false), res, data)
eq(a85decode(base64, decode(data, "ascii"), false), res, data)
eq(a85decode(base64, append!((b"<~" + data), b"~>"), true), res, data)
eq(a85decode(base64, data + b"~>", true), res, data)
eq(a85decode(base64, "<~%s~>" % decode(data, "ascii"), true), res, data)
end
eq(a85decode(base64, b"yy", true, false), repeat(b" ",8))
eq(a85decode(base64, b"y+<Vd", true, false), repeat(b" ",7))
eq(a85decode(base64, b"y+<U", true, false), repeat(b" ",6))
eq(a85decode(base64, b"y+9", true, false), repeat(b" ",5))
check_other_types(self, base64.a85decode, b"GB\\6`E-ZP=Df.1GEb>", b"www.python.org")
end

function test_b85decode(self::BaseXYTestCase)
eq = self.assertEqual
tests = Dict(b"" => b"", b"cXxL#aCvlSZ*DGca%T" => b"www.python.org", b"009C61O)~M2nh-c3=Iws5D^j+6crX17#SKH9337XAR!_nBqb&%C@Cr{EG;fCFflSSG&MFiI5|2yJUu=?KtV!7L`6nNNJ&adOifNtP*GA-R8>}2SXo+ITwPvYU}0ioWMyV&XlZI|Y;A6DaB*^Tbai%jczJqze0_d@fPsR8goTEOh>41ejE#<ukdcy;l$Dm3n3<ZJoSmMZprN9pq@|{(sHv)}tgWuEu(7hUw6(UkxVgH!yuH4^z`?@9#Kp$P$jQpf%+1cv(9zP<)YaD4*xB0K+}+;a;Njxq<mKk)=;`X~?CtLF@bU8V^!4`l`1$(#{Qdp" => bytes(0:254), b"VPa!sWoBn+X=-b1ZEkOHadLBXb#`}nd3r%YLqtVJM@UIZOH55pPf$@(Q&d$}S6EqEFflSSG&MFiI5{CeBQRbjDkv#CIy^osE+AW7dwl" => b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#0^&*();:<>,. []{}", b"Zf_uPVPs@!Zf7no" => b"no padding..", b"dS!BNAY*TBaB^jHb7^mG00000" => b"zero compression\x00\x00\x00\x00", b"dS!BNAY*TBaB^jHb7^mG0000" => b"zero compression\x00\x00\x00", b"LT`0$WMOi7IsgCw00" => b"Boundary:\x00\x00\x00\x00", b"Q*dEpWgug3ZE$irARr(h" => b"Space compr:    ", b"{{" => b"\xff", b"|Nj" => repeat(b"\xff",2), b"|Ns9" => repeat(b"\xff",3), b"|NsC0" => repeat(b"\xff",4))
for (data, res) in items(tests)
eq(b85decode(base64, data), res)
eq(b85decode(base64, decode(data, "ascii")), res)
end
check_other_types(self, base64.b85decode, b"cXxL#aCvlSZ*DGca%T", b"www.python.org")
end

function test_a85_padding(self::BaseXYTestCase)
eq = self.assertEqual
eq(a85encode(base64, b"x", true), b"GQ7^D")
eq(a85encode(base64, b"xx", true), b"G^'2g")
eq(a85encode(base64, b"xxx", true), b"G^+H5")
eq(a85encode(base64, b"xxxx", true), b"G^+IX")
eq(a85encode(base64, b"xxxxx", true), b"G^+IXGQ7^D")
eq(a85decode(base64, b"GQ7^D"), b"x\x00\x00\x00")
eq(a85decode(base64, b"G^'2g"), b"xx\x00\x00")
eq(a85decode(base64, b"G^+H5"), b"xxx\x00")
eq(a85decode(base64, b"G^+IX"), b"xxxx")
eq(a85decode(base64, b"G^+IXGQ7^D"), b"xxxxx\x00\x00\x00")
end

function test_b85_padding(self::BaseXYTestCase)
eq = self.assertEqual
eq(b85encode(base64, b"x", true), b"cmMzZ")
eq(b85encode(base64, b"xx", true), b"cz6H+")
eq(b85encode(base64, b"xxx", true), b"czAdK")
eq(b85encode(base64, b"xxxx", true), b"czAet")
eq(b85encode(base64, b"xxxxx", true), b"czAetcmMzZ")
eq(b85decode(base64, b"cmMzZ"), b"x\x00\x00\x00")
eq(b85decode(base64, b"cz6H+"), b"xx\x00\x00")
eq(b85decode(base64, b"czAdK"), b"xxx\x00")
eq(b85decode(base64, b"czAet"), b"xxxx")
eq(b85decode(base64, b"czAetcmMzZ"), b"xxxxx\x00\x00\x00")
end

function test_a85decode_errors(self::BaseXYTestCase)
illegal = (set(0:31) | set(118:255)) - set(b" \t\n\r\x0b")
for c in illegal
@test_throws ValueError bytes([c])() do 
a85decode(base64, append!(b"!!!!", bytes([c])))
end
@test_throws ValueError bytes([c])() do 
a85decode(base64, append!(b"!!!!", bytes([c])), false)
end
@test_throws ValueError bytes([c])() do 
a85decode(base64, append!(append!(b"<~!!!!", bytes([c])), b"~>"), true)
end
end
@test_throws ValueError base64.a85decode(b"malformed", true)
@test_throws ValueError base64.a85decode(b"<~still malformed", true)
@test_throws ValueError base64.a85decode(b"<~~>")
@test_throws ValueError base64.a85decode(b"<~~>", false)
a85decode(base64, b"<~~>", true)
@test_throws ValueError base64.a85decode(b"abcx", false)
@test_throws ValueError base64.a85decode(b"abcdey", false)
@test_throws ValueError base64.a85decode(b"a b\nc", false, b"")
@test_throws ValueError base64.a85decode(b"s", false)
@test_throws ValueError base64.a85decode(b"s8", false)
@test_throws ValueError base64.a85decode(b"s8W", false)
@test_throws ValueError base64.a85decode(b"s8W-", false)
@test_throws ValueError base64.a85decode(b"s8W-\"", false)
end

function test_b85decode_errors(self::BaseXYTestCase)
illegal = append!(append!(collect(0:32), collect(b"\"\',./:[\\]")), collect(128:255))
for c in illegal
@test_throws ValueError bytes([c])() do 
b85decode(base64, append!(b"0000", bytes([c])))
end
end
@test_throws ValueError base64.b85decode(b"|")
@test_throws ValueError base64.b85decode(b"|N")
@test_throws ValueError base64.b85decode(b"|Ns")
@test_throws ValueError base64.b85decode(b"|NsC")
@test_throws ValueError base64.b85decode(b"|NsC1")
end

function test_decode_nonascii_str(self::BaseXYTestCase)
decode_funcs = (base64.b64decode, base64.standard_b64decode, base64.urlsafe_b64decode, base64.b32decode, base64.b16decode, base64.b85decode, base64.a85decode)
for f in decode_funcs
@test_throws ValueError f("with non-ascii Ë")
end
end

function test_ErrorHeritage(self::BaseXYTestCase)
@test binascii.Error <: ValueError
end

function test_RFC4648_test_cases(self::BaseXYTestCase)
b64encode = base64.b64encode
b32hexencode = base64.b32hexencode
b32encode = base64.b32encode
b16encode = base64.b16encode
@test (b64encode(b"") == b"")
@test (b64encode(b"f") == b"Zg==")
@test (b64encode(b"fo") == b"Zm8=")
@test (b64encode(b"foo") == b"Zm9v")
@test (b64encode(b"foob") == b"Zm9vYg==")
@test (b64encode(b"fooba") == b"Zm9vYmE=")
@test (b64encode(b"foobar") == b"Zm9vYmFy")
@test (b32encode(b"") == b"")
@test (b32encode(b"f") == b"MY======")
@test (b32encode(b"fo") == b"MZXQ====")
@test (b32encode(b"foo") == b"MZXW6===")
@test (b32encode(b"foob") == b"MZXW6YQ=")
@test (b32encode(b"fooba") == b"MZXW6YTB")
@test (b32encode(b"foobar") == b"MZXW6YTBOI======")
@test (b32hexencode(b"") == b"")
@test (b32hexencode(b"f") == b"CO======")
@test (b32hexencode(b"fo") == b"CPNG====")
@test (b32hexencode(b"foo") == b"CPNMU===")
@test (b32hexencode(b"foob") == b"CPNMUOG=")
@test (b32hexencode(b"fooba") == b"CPNMUOJ1")
@test (b32hexencode(b"foobar") == b"CPNMUOJ1E8======")
@test (b16encode(b"") == b"")
@test (b16encode(b"f") == b"66")
@test (b16encode(b"fo") == b"666F")
@test (b16encode(b"foo") == b"666F6F")
@test (b16encode(b"foob") == b"666F6F62")
@test (b16encode(b"fooba") == b"666F6F6261")
@test (b16encode(b"foobar") == b"666F6F626172")
end

mutable struct TestMain <: AbstractTestMain

end
function tearDown(self::TestMain)
if exists(os.path, os_helper.TESTFN)
std::fs::remove_file(os_helper.TESTFN)
end
end

function get_output(self::TestMain)
return assert_python_ok(script_helper, "-m", "base64", args...).out
end

function test_encode_decode(self::TestMain)
output = get_output(self)
assertSequenceEqual(self, splitlines(output), (b"b'Aladdin:open sesame'", b"b'QWxhZGRpbjpvcGVuIHNlc2FtZQ==\\n'", b"b'Aladdin:open sesame'"))
end

function test_encode_file(self::TestMain)
readline(os_helper.TESTFN) do fp 
write(fp, b"a\xffb\n")
end
output = get_output(self)
@test (rstrip(output) == b"Yf9iCg==")
end

function test_encode_from_stdin(self::TestMain)
spawn_python(script_helper, "-m", "base64", "-e") do proc 
out, err = communicate(proc, b"a\xffb\n")
end
@test (rstrip(out) == b"Yf9iCg==")
assertIsNone(self, err)
end

function test_decode(self::TestMain)
readline(os_helper.TESTFN) do fp 
write(fp, b"Yf9iCg==")
end
output = get_output(self)
@test (rstrip(output) == b"a\xffb")
end

function main()
legacy_base64_test_case = LegacyBase64TestCase()
check_type_errors(legacy_base64_test_case)
test_encodebytes(legacy_base64_test_case)
test_decodebytes(legacy_base64_test_case)
test_encode(legacy_base64_test_case)
test_decode(legacy_base64_test_case)
base_x_y_test_case = BaseXYTestCase()
check_encode_type_errors(base_x_y_test_case)
check_decode_type_errors(base_x_y_test_case)
check_other_types(base_x_y_test_case)
check_multidimensional(base_x_y_test_case)
check_nonbyte_element_format(base_x_y_test_case)
test_b64encode(base_x_y_test_case)
test_b64decode(base_x_y_test_case)
test_b64decode_padding_error(base_x_y_test_case)
test_b64decode_invalid_chars(base_x_y_test_case)
test_b32encode(base_x_y_test_case)
test_b32decode(base_x_y_test_case)
test_b32decode_casefold(base_x_y_test_case)
test_b32decode_error(base_x_y_test_case)
test_b32hexencode(base_x_y_test_case)
test_b32hexencode_other_types(base_x_y_test_case)
test_b32hexdecode(base_x_y_test_case)
test_b32hexdecode_other_types(base_x_y_test_case)
test_b32hexdecode_error(base_x_y_test_case)
test_b16encode(base_x_y_test_case)
test_b16decode(base_x_y_test_case)
test_a85encode(base_x_y_test_case)
test_b85encode(base_x_y_test_case)
test_a85decode(base_x_y_test_case)
test_b85decode(base_x_y_test_case)
test_a85_padding(base_x_y_test_case)
test_b85_padding(base_x_y_test_case)
test_a85decode_errors(base_x_y_test_case)
test_b85decode_errors(base_x_y_test_case)
test_decode_nonascii_str(base_x_y_test_case)
test_ErrorHeritage(base_x_y_test_case)
test_RFC4648_test_cases(base_x_y_test_case)
test_main = TestMain()
tearDown(test_main)
get_output(test_main)
test_encode_decode(test_main)
test_encode_file(test_main)
test_encode_from_stdin(test_main)
test_decode(test_main)
end

main()