using Test

import string
using string: Template
abstract type AbstractModuleTest end
abstract type AbstractAnyAttr end
abstract type AbstractNamespaceFormatter <: Abstractstring.Formatter end
abstract type AbstractCallFormatter <: Abstractstring.Formatter end
abstract type AbstractXFormatter <: Abstractstring.Formatter end
abstract type AbstractBarFormatter <: Abstractstring.Formatter end
abstract type AbstractCheckAllUsedFormatter <: Abstractstring.Formatter end
abstract type AbstractBag end
abstract type AbstractMapping end
abstract type AbstractTestTemplate end
abstract type AbstractPathPattern <: AbstractTemplate end
abstract type AbstractMyPattern <: AbstractTemplate end
abstract type AbstractBadPattern <: AbstractTemplate end
abstract type AbstractMyTemplate <: AbstractTemplate end
abstract type AbstractAmpersandTemplate <: AbstractTemplate end
abstract type AbstractPieDelims <: AbstractTemplate end
mutable struct ModuleTest <: AbstractModuleTest
namespace
end
function test_attrs(self::ModuleTest)
@test (string.whitespace == " \t\n\r\v\f")
@test (string.ascii_lowercase == "abcdefghijklmnopqrstuvwxyz")
@test (string.ascii_uppercase == "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
@test (string.ascii_letters == string.ascii_lowercase + string.ascii_uppercase)
@test (string.digits == "0123456789")
@test (string.hexdigits == string.digits + "abcdefABCDEF")
@test (string.octdigits == "01234567")
@test (string.punctuation == "!\"#\$%&\'()*+,-./:;<=>?@[\\]^_`{|}~")
@test (string.printable == (((string.digits + string.ascii_lowercase) + string.ascii_uppercase) + string.punctuation) + string.whitespace)
end

function test_capwords(self::ModuleTest)
@test (capwords(string, "abc def ghi") == "Abc Def Ghi")
@test (capwords(string, "abc\tdef\nghi") == "Abc Def Ghi")
@test (capwords(string, "abc\t   def  \nghi") == "Abc Def Ghi")
@test (capwords(string, "ABC DEF GHI") == "Abc Def Ghi")
@test (capwords(string, "ABC-DEF-GHI", "-") == "Abc-Def-Ghi")
@test (capwords(string, "ABC-def DEF-ghi GHI") == "Abc-def Def-ghi Ghi")
@test (capwords(string, "   aBc  DeF   ") == "Abc Def")
@test (capwords(string, "\taBc\tDeF\t") == "Abc Def")
@test (capwords(string, "\taBc\tDeF\t", "\t") == "\tAbc\tDef\t")
end

function test_basic_formatter(self::ModuleTest)
fmt = Formatter(string)
@test (fmt == "foo")
@test (fmt == "foobar")
@test (fmt == "foo6bar-6")
@test_throws TypeError fmt()
@test_throws TypeError string.Formatter()
end

function test_format_keyword_arguments(self::ModuleTest)
fmt = Formatter(string)
@test (fmt == "-test-")
@test_throws KeyError fmt("-{arg}-")
@test (fmt == "-test-")
@test_throws KeyError fmt("-{self}-")
@test (fmt == "-test-")
@test_throws KeyError fmt("-{format_string}-")
assertRaisesRegex(self, TypeError, "format_string") do 
fmt
end
end

function test_auto_numbering(self::ModuleTest)
fmt = Formatter(string)
@test (fmt == "foo$()$()")
@test (fmt == "foo$(1)$(num)$(1)")
@test (fmt == "$(:^)$()")
@test (fmt == "$(:^)$() $()")
@test (fmt == "$(:^)pad$()$()")
assertRaises(self, ValueError) do 
fmt
end
assertRaises(self, ValueError) do 
fmt
end
end

function test_conversion_specifiers(self::ModuleTest)
fmt = Formatter(string)
@test (fmt == "-\'test\'-")
@test (fmt == "test")
@test_throws ValueError fmt("{0!h}", "test")
@test (fmt == "42")
@test (fmt == "\'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ\'")
@test (fmt == "\'\\xff\'")
@test (fmt == "\'\\u0100\'")
end

function test_name_lookup(self::AnyAttr)
fmt = Formatter(string)
mutable struct AnyAttr <: AbstractAnyAttr

end
function __getattr__(self::AnyAttr, attr)
return attr
end

x = AnyAttr()
assertEqual(self, fmt, "lumberjack")
assertRaises(self, AttributeError) do 
fmt
end
end

function test_index_lookup(self::ModuleTest)
fmt = Formatter(string)
lookup = ["eggs", "and", "spam"]
@test (fmt == "spameggs")
assertRaises(self, IndexError) do 
fmt
end
assertRaises(self, KeyError) do 
fmt
end
end

function test_override_get_value(self::NamespaceFormatter)
mutable struct NamespaceFormatter <: AbstractNamespaceFormatter
namespace

            NamespaceFormatter(namespace = Dict()) = begin
                string.Formatter.__init__(self)
                new(namespace )
            end
end
function get_value(self::NamespaceFormatter, key, args, kwds)
if isa(key, str)
try
return kwds[key + 1]
catch exn
if exn isa KeyError
return self.namespace[key + 1]
end
end
else
get_value(string.Formatter, key, args, kwds)
end
end

fmt = NamespaceFormatter(Dict("greeting" => "hello"))
assertEqual(self, fmt, "hello, world!")
end

function test_override_format_field(self::CallFormatter)
mutable struct CallFormatter <: AbstractCallFormatter

end
function format_field(self::CallFormatter, value, format_spec)
return value()
end

fmt = CallFormatter()
assertEqual(self, fmt, "*result*")
end

function test_override_convert_field(self::XFormatter)
mutable struct XFormatter <: AbstractXFormatter

end
function convert_field(self::XFormatter, value, conversion)
if conversion == "x"
return nothing
end
return convert_field(super(), value, conversion)
end

fmt = XFormatter()
assertEqual(self, fmt, "\'foo\':None")
end

function test_override_parse(self::BarFormatter)
mutable struct BarFormatter <: AbstractBarFormatter

end
function parse(self::BarFormatter, format_string)
Channel() do ch_parse 
for field in split(format_string, "|")
if field[1] == "+"
field_name, _, format_spec = partition(field[2:end], ":")
put!(ch_parse, ("", field_name, format_spec, nothing))
else
put!(ch_parse, (field, nothing, nothing, nothing))
end
end
end
end

fmt = BarFormatter()
assertEqual(self, fmt, "*   foo    *")
end

function test_check_unused_args(self::CheckAllUsedFormatter)
mutable struct CheckAllUsedFormatter <: AbstractCheckAllUsedFormatter

end
function check_unused_args(self::CheckAllUsedFormatter, used_args, args, kwargs)
unused_args = set(keys(kwargs))
update(unused_args, 0:length(args) - 1)
for arg in used_args
remove(unused_args, arg)
end
if unused_args
throw(ValueError("unused arguments"))
end
end

fmt = CheckAllUsedFormatter()
assertEqual(self, fmt, "10")
assertEqual(self, fmt, "10100")
assertEqual(self, fmt, "1010020")
assertRaises(self, ValueError, fmt, "{0}{i}{1}", 10, 20, 100, 0)
assertRaises(self, ValueError, fmt, "{0}", 10, 20)
assertRaises(self, ValueError, fmt, "{0}", 10, 20, 100)
assertRaises(self, ValueError, fmt, "{i}", 10, 20, 100)
end

function test_vformat_recursion_limit(self::ModuleTest)
fmt = Formatter(string)
args = ()
kwargs = dict(100)
assertRaises(self, ValueError) do err 
_vformat(fmt, "{i}", args, kwargs, set(), -1)
end
assertIn(self, "recursion", string(err.exception))
end

mutable struct Bag <: AbstractBag

end

mutable struct Mapping <: AbstractMapping

end
function __getitem__(self::Mapping, name)
obj = self
for part in split(name, ".")
try
obj = getfield(obj, part
catch exn
if exn isa AttributeError
throw(KeyError(name))
end
end
end
return obj
end

mutable struct TestTemplate <: AbstractTestTemplate
braceidpattern::String
delimiter::String
flags::Int64
idpattern::String
pattern::String

                    TestTemplate(braceidpattern::String = "[A-Z]+", delimiter::String = "&", flags::Int64 = 0, idpattern::String = "[_a-z][._a-z0-9]*", pattern::String = "\n            (?P<escaped>@{2})                   |\n            @(?P<named>[_a-z][._a-z0-9]*)       |\n            @{(?P<braced>[_a-z][._a-z0-9]*)}    |\n            (?P<invalid>@)\n            ") =
                        new(braceidpattern, delimiter, flags, idpattern, pattern)
end
function test_regular_templates(self::TestTemplate)
s = Template("\$who likes to eat a bag of \$what worth \$\$100")
@test (substitute(s, dict("tim", "ham")) == "tim likes to eat a bag of ham worth \$100")
@test_throws KeyError s.substitute(dict("tim"))
@test_throws TypeError Template.substitute()
end

function test_regular_templates_with_braces(self::TestTemplate)
s = Template("\$who likes \${what} for \${meal}")
d = dict("tim", "ham", "dinner")
@test (substitute(s, d) == "tim likes ham for dinner")
@test_throws KeyError s.substitute(dict("tim", "ham"))
end

function test_regular_templates_with_upper_case(self::TestTemplate)
s = Template("\$WHO likes \${WHAT} for \${MEAL}")
d = dict("tim", "ham", "dinner")
@test (substitute(s, d) == "tim likes ham for dinner")
end

function test_regular_templates_with_non_letters(self::TestTemplate)
s = Template("\$_wh0_ likes \${_w_h_a_t_} for \${mea1}")
d = dict("tim", "ham", "dinner")
@test (substitute(s, d) == "tim likes ham for dinner")
end

function test_escapes(self::TestTemplate)
eq = self.assertEqual
s = Template("\$who likes to eat a bag of \$\$what worth \$\$100")
eq(substitute(s, dict("tim", "ham")), "tim likes to eat a bag of \$what worth \$100")
s = Template("\$who likes \$\$")
eq(substitute(s, dict("tim", "ham")), "tim likes \$")
end

function test_percents(self::TestTemplate)
eq = self.assertEqual
s = Template("%(foo)s \$foo \${foo}")
d = dict("baz")
eq(substitute(s, d), "%(foo)s baz baz")
eq(safe_substitute(s, d), "%(foo)s baz baz")
end

function test_stringification(self::TestTemplate)
eq = self.assertEqual
s = Template("tim has eaten \$count bags of ham today")
d = dict(7)
eq(substitute(s, d), "tim has eaten 7 bags of ham today")
eq(safe_substitute(s, d), "tim has eaten 7 bags of ham today")
s = Template("tim has eaten \${count} bags of ham today")
eq(substitute(s, d), "tim has eaten 7 bags of ham today")
end

function test_tupleargs(self::TestTemplate)
eq = self.assertEqual
s = Template("\$who ate \${meal}")
d = dict(("tim", "fred"), ("ham", "kung pao"))
eq(substitute(s, d), "(\'tim\', \'fred\') ate (\'ham\', \'kung pao\')")
eq(safe_substitute(s, d), "(\'tim\', \'fred\') ate (\'ham\', \'kung pao\')")
end

function test_SafeTemplate(self::TestTemplate)
eq = self.assertEqual
s = Template("\$who likes \${what} for \${meal}")
eq(safe_substitute(s, dict("tim")), "tim likes \${what} for \${meal}")
eq(safe_substitute(s, dict("ham")), "\$who likes ham for \${meal}")
eq(safe_substitute(s, dict("ham", "dinner")), "\$who likes ham for dinner")
eq(safe_substitute(s, dict("tim", "ham")), "tim likes ham for \${meal}")
eq(safe_substitute(s, dict("tim", "ham", "dinner")), "tim likes ham for dinner")
end

function test_invalid_placeholders(self::TestTemplate)
raises = self.assertRaises
s = Template("\$who likes \$")
raises(ValueError, s.substitute, dict("tim"))
s = Template("\$who likes \${what)")
raises(ValueError, s.substitute, dict("tim"))
s = Template("\$who likes \$100")
raises(ValueError, s.substitute, dict("tim"))
s = Template("\$who likes \$ı")
raises(ValueError, s.substitute, dict("tim"))
s = Template("\$who likes \$İ")
raises(ValueError, s.substitute, dict("tim"))
end

function test_idpattern_override(self::PathPattern)
mutable struct PathPattern <: AbstractPathPattern
idpattern::String

                    PathPattern(idpattern::String = "[_a-z][._a-z0-9]*") =
                        new(idpattern)
end

m = Mapping()
m.bag = Bag()
m.bag.foo = Bag()
m.bag.foo.who = "tim"
m.bag.what = "ham"
s = PathPattern("\$bag.foo.who likes to eat a bag of \$bag.what")
assertEqual(self, substitute(s, m), "tim likes to eat a bag of ham")
end

function test_flags_override(self::MyPattern)
mutable struct MyPattern <: AbstractMyPattern
flags::Int64

                    MyPattern(flags::Int64 = 0) =
                        new(flags)
end

s = MyPattern("\$wHO likes \${WHAT} for \${meal}")
d = dict("tim", "ham", "dinner", "fred")
assertRaises(self, ValueError, s.substitute, d)
assertEqual(self, safe_substitute(s, d), "fredHO likes \${WHAT} for dinner")
end

function test_idpattern_override_inside_outside(self::MyPattern)
mutable struct MyPattern <: AbstractMyPattern
braceidpattern::String
flags::Int64
idpattern::String

                    MyPattern(braceidpattern::String = "[A-Z]+", flags::Int64 = 0, idpattern::String = "[a-z]+") =
                        new(braceidpattern, flags, idpattern)
end

m = dict("foo", "BAR")
s = MyPattern("\$foo \${BAR}")
assertEqual(self, substitute(s, m), "foo BAR")
end

function test_idpattern_override_inside_outside_invalid_unbraced(self::MyPattern)
mutable struct MyPattern <: AbstractMyPattern
braceidpattern::String
flags::Int64
idpattern::String

                    MyPattern(braceidpattern::String = "[A-Z]+", flags::Int64 = 0, idpattern::String = "[a-z]+") =
                        new(braceidpattern, flags, idpattern)
end

m = dict("foo", "BAR")
s = MyPattern("\$FOO")
assertRaises(self, ValueError, s.substitute, m)
s = MyPattern("\${bar}")
assertRaises(self, ValueError, s.substitute, m)
end

function test_pattern_override(self::BadPattern)
mutable struct MyPattern <: AbstractMyPattern
pattern::String

                    MyPattern(pattern::String = "\n            (?P<escaped>@{2})                   |\n            @(?P<named>[_a-z][._a-z0-9]*)       |\n            @{(?P<braced>[_a-z][._a-z0-9]*)}    |\n            (?P<invalid>@)\n            ") =
                        new(pattern)
end

m = Mapping()
m.bag = Bag()
m.bag.foo = Bag()
m.bag.foo.who = "tim"
m.bag.what = "ham"
s = MyPattern("@bag.foo.who likes to eat a bag of @bag.what")
assertEqual(self, substitute(s, m), "tim likes to eat a bag of ham")
mutable struct BadPattern <: AbstractBadPattern
pattern::String

                    BadPattern(pattern::String = "\n            (?P<badname>.*)                     |\n            (?P<escaped>@{2})                   |\n            @(?P<named>[_a-z][._a-z0-9]*)       |\n            @{(?P<braced>[_a-z][._a-z0-9]*)}    |\n            (?P<invalid>@)                      |\n            ") =
                        new(pattern)
end

s = BadPattern("@bag.foo.who likes to eat a bag of @bag.what")
assertRaises(self, ValueError, s.substitute, Dict())
assertRaises(self, ValueError, s.safe_substitute, Dict())
end

function test_braced_override(self::MyTemplate)
mutable struct MyTemplate <: AbstractMyTemplate
pattern::String

                    MyTemplate(pattern::String = "\n            \\\$(?:\n              (?P<escaped>\$)                     |\n              (?P<named>[_a-z][_a-z0-9]*)        |\n              @@(?P<braced>[_a-z][_a-z0-9]*)@@   |\n              (?P<invalid>)                      |\n           )\n           ") =
                        new(pattern)
end

tmpl = "PyCon in \$@@location@@"
t = MyTemplate(tmpl)
assertRaises(self, KeyError, t.substitute, Dict())
val = substitute(t, Dict("location" => "Cleveland"))
assertEqual(self, val, "PyCon in Cleveland")
end

function test_braced_override_safe(self::MyTemplate)
mutable struct MyTemplate <: AbstractMyTemplate
pattern::String

                    MyTemplate(pattern::String = "\n            \\\$(?:\n              (?P<escaped>\$)                     |\n              (?P<named>[_a-z][_a-z0-9]*)        |\n              @@(?P<braced>[_a-z][_a-z0-9]*)@@   |\n              (?P<invalid>)                      |\n           )\n           ") =
                        new(pattern)
end

tmpl = "PyCon in \$@@location@@"
t = MyTemplate(tmpl)
assertEqual(self, safe_substitute(t), tmpl)
val = safe_substitute(t, Dict("location" => "Cleveland"))
assertEqual(self, val, "PyCon in Cleveland")
end

function test_invalid_with_no_lines(self::MyTemplate)
mutable struct MyTemplate <: AbstractMyTemplate
pattern::String

                    MyTemplate(pattern::String = "\n              (?P<invalid>) |\n              unreachable(\n                (?P<named>)   |\n                (?P<braced>)  |\n                (?P<escaped>)\n              )\n            ") =
                        new(pattern)
end

s = MyTemplate("")
assertRaises(self, ValueError) do err 
substitute(s, Dict())
end
assertIn(self, "line 1, col 1", string(err.exception))
end

function test_unicode_values(self::TestTemplate)
s = Template("\$who likes \$what")
d = dict("tÿm", "fþ\fed")
@test (substitute(s, d) == "tÿm likes fþ\fed")
end

function test_keyword_arguments(self::TestTemplate)
eq = self.assertEqual
s = Template("\$who likes \$what")
eq(substitute(s, "tim", "ham"), "tim likes ham")
eq(substitute(s, dict("tim"), "ham"), "tim likes ham")
eq(substitute(s, dict("fred", "kung pao"), "tim", "ham"), "tim likes ham")
s = Template("the mapping is \$mapping")
eq(substitute(s, dict("none"), "bozo"), "the mapping is bozo")
eq(substitute(s, dict("one"), "two"), "the mapping is two")
s = Template("the self is \$self")
eq(substitute(s, "bozo"), "the self is bozo")
end

function test_keyword_arguments_safe(self::TestTemplate)
eq = self.assertEqual
raises = self.assertRaises
s = Template("\$who likes \$what")
eq(safe_substitute(s, "tim", "ham"), "tim likes ham")
eq(safe_substitute(s, dict("tim"), "ham"), "tim likes ham")
eq(safe_substitute(s, dict("fred", "kung pao"), "tim", "ham"), "tim likes ham")
s = Template("the mapping is \$mapping")
eq(safe_substitute(s, dict("none"), "bozo"), "the mapping is bozo")
eq(safe_substitute(s, dict("one"), "two"), "the mapping is two")
d = dict("one")
raises(TypeError, s.substitute, d, Dict())
raises(TypeError, s.safe_substitute, d, Dict())
s = Template("the self is \$self")
eq(safe_substitute(s, "bozo"), "the self is bozo")
end

function test_delimiter_override(self::PieDelims)
eq = self.assertEqual
raises = self.assertRaises
mutable struct AmpersandTemplate <: AbstractAmpersandTemplate
delimiter::String

                    AmpersandTemplate(delimiter::String = "&") =
                        new(delimiter)
end

s = AmpersandTemplate("this &gift is for &{who} &&")
eq(substitute(s, "bud", "you"), "this bud is for you &")
raises(KeyError, s.substitute)
eq(safe_substitute(s, "bud", "you"), "this bud is for you &")
eq(safe_substitute(s), "this &gift is for &{who} &")
s = AmpersandTemplate("this &gift is for &{who} &")
raises(ValueError, s.substitute, dict("bud", "you"))
eq(safe_substitute(s), "this &gift is for &{who} &")
mutable struct PieDelims <: AbstractPieDelims
delimiter::String

                    PieDelims(delimiter::String = "@") =
                        new(delimiter)
end

s = PieDelims("@who likes to eat a bag of @{what} worth \$100")
assertEqual(self, substitute(s, dict("tim", "ham")), "tim likes to eat a bag of ham worth \$100")
end

function main()
module_test = ModuleTest()
test_attrs(module_test)
test_capwords(module_test)
test_basic_formatter(module_test)
test_format_keyword_arguments(module_test)
test_auto_numbering(module_test)
test_conversion_specifiers(module_test)
test_name_lookup(module_test)
test_index_lookup(module_test)
test_override_get_value(module_test)
test_override_format_field(module_test)
test_override_convert_field(module_test)
test_override_parse(module_test)
test_check_unused_args(module_test)
test_vformat_recursion_limit(module_test)
test_template = TestTemplate()
test_regular_templates(test_template)
test_regular_templates_with_braces(test_template)
test_regular_templates_with_upper_case(test_template)
test_regular_templates_with_non_letters(test_template)
test_escapes(test_template)
test_percents(test_template)
test_stringification(test_template)
test_tupleargs(test_template)
test_SafeTemplate(test_template)
test_invalid_placeholders(test_template)
test_idpattern_override(test_template)
test_flags_override(test_template)
test_idpattern_override_inside_outside(test_template)
test_idpattern_override_inside_outside_invalid_unbraced(test_template)
test_pattern_override(test_template)
test_braced_override(test_template)
test_braced_override_safe(test_template)
test_invalid_with_no_lines(test_template)
test_unicode_values(test_template)
test_keyword_arguments(test_template)
test_keyword_arguments_safe(test_template)
test_delimiter_override(test_template)
end

main()