#= Unit tests for the keyword only argument specified in PEP 3102. =#
using Test
__author__ = "Jiwon Seo"
abstract type AbstractFoo end
abstract type AbstractKeywordOnlyArgTestCase end
abstract type AbstractExample end
abstract type AbstractX end
__email__ = "seojiwon at gmail dot com"

function posonly_sum(pos_arg1)::Any
return (pos_arg1 + sum(arg)) + sum(values(kwarg))
end

function keywordonly_sum()::Any
return k1 + k2
end

function keywordonly_nodefaults_sum()::Any
return k1 + k2
end

function keywordonly_and_kwarg_sum()::Any
return (k1 + k2) + sum(values(kwarg))
end

function mixedargs_sum(a, b = 0)::Any
return (((a + b) + k1) + k2) + sum(arg)
end

function mixedargs_sum2(a, b = 0)::Any
return ((((a + b) + k1) + k2) + sum(arg)) + sum(values(kwargs))
end

function sortnum()
return sorted(collect(nums), reverse)
end

function sortwords()
return sorted(collect(words), reverse)
end

mutable struct Foo <: AbstractFoo
k1
k2
end
function set(self::Foo, p1)
self.k1 = k1
self.k2 = k2
end

function sum(self::Foo)::Any
return self.k1 + self.k2
end

mutable struct KeywordOnlyArgTestCase <: AbstractKeywordOnlyArgTestCase

end
function assertRaisesSyntaxError(self::KeywordOnlyArgTestCase, codestr)
function shouldRaiseSyntaxError(s)
compile(s, "<test>", "single")
end

@test_throws SyntaxError shouldRaiseSyntaxError(codestr)
end

function testSyntaxErrorForFunctionDefinition(self::KeywordOnlyArgTestCase)
assertRaisesSyntaxError(self, "def f(p, *):\n  pass\n")
assertRaisesSyntaxError(self, "def f(p1, *, p1=100):\n  pass\n")
assertRaisesSyntaxError(self, "def f(p1, *k1, k1=100):\n  pass\n")
assertRaisesSyntaxError(self, "def f(p1, *, k1, k1=100):\n  pass\n")
assertRaisesSyntaxError(self, "def f(p1, *, **k1):\n  pass\n")
assertRaisesSyntaxError(self, "def f(p1, *, k1, **k1):\n  pass\n")
assertRaisesSyntaxError(self, "def f(p1, *, None, **k1):\n  pass\n")
assertRaisesSyntaxError(self, "def f(p, *, (k1, k2), **kw):\n  pass\n")
end

function testSyntaxForManyArguments(self::KeywordOnlyArgTestCase)
fundef = "def f(%s):\n  pass\n" % join(("i%d" % i for i in 0:299), ", ")
compile(fundef, "<test>", "single")
fundef = "def f(*, %s):\n  pass\n" % join(("i%d" % i for i in 0:299), ", ")
compile(fundef, "<test>", "single")
end

function testTooManyPositionalErrorMessage(self::KeywordOnlyArgTestCase)
function f(a, b = nothing)
#= pass =#
end

assertRaises(self, TypeError) do exc 
f(1, 2)
end
expected = "$(f.__qualname__)() takes from 1 to 2 positional arguments but 3 were given"
@test (string(exc.exception) == expected)
end

function testSyntaxErrorForFunctionCall(self::KeywordOnlyArgTestCase)
assertRaisesSyntaxError(self, "f(p, k=1, p2)")
assertRaisesSyntaxError(self, "f(p, k1=50, *(1,2), k1=100)")
end

function testRaiseErrorFuncallWithUnexpectedKeywordArgument(self::KeywordOnlyArgTestCase)
@test_throws TypeError keywordonly_sum(())
@test_throws TypeError keywordonly_nodefaults_sum(())
@test_throws TypeError Foo(())
try
keywordonly_sum()
fail(self, "should raise TypeError")
catch exn
if exn isa TypeError
#= pass =#
end
end
try
keywordonly_nodefaults_sum()
fail(self, "should raise TypeError")
catch exn
if exn isa TypeError
#= pass =#
end
end
end

function testFunctionCall(self::KeywordOnlyArgTestCase)
@test (1 == posonly_sum(1))
@test (1 + 2 == posonly_sum(1))
@test ((1 + 2) + 3 == posonly_sum(1))
@test (((1 + 2) + 3) + 4 == posonly_sum(1))
@test (1 == keywordonly_sum())
@test (1 + 2 == keywordonly_sum())
@test (1 + 2 == keywordonly_and_kwarg_sum())
@test ((1 + 2) + 3 == keywordonly_and_kwarg_sum())
@test (((1 + 2) + 3) + 4 == keywordonly_and_kwarg_sum())
@test (1 + 2 == mixedargs_sum(1))
@test ((1 + 2) + 3 == mixedargs_sum(1, 2))
@test (((1 + 2) + 3) + 4 == mixedargs_sum(1, 2))
@test ((((1 + 2) + 3) + 4) + 5 == mixedargs_sum(1, 2))
@test (1 + 2 == mixedargs_sum2(1))
@test ((1 + 2) + 3 == mixedargs_sum2(1, 2))
@test (((1 + 2) + 3) + 4 == mixedargs_sum2(1, 2))
@test ((((1 + 2) + 3) + 4) + 5 == mixedargs_sum2(1, 2))
@test (((((1 + 2) + 3) + 4) + 5) + 6 == mixedargs_sum2(1, 2))
@test (((((1 + 2) + 3) + 4) + 5) + 6 == mixedargs_sum2(1, 2))
@test (1 == sum(Foo(1)))
@test (1 + 2 == sum(Foo(1, 2)))
@test ([1, 2, 3] == sortnum())
@test ([3, 2, 1] == sortnum())
@test (["a", "b", "c"] == sortwords())
@test (["c", "b", "a"] == sortwords())
@test (["c", "b", "a"] == sortwords())
end

function testKwDefaults(self::KeywordOnlyArgTestCase)
function foo(p1, p2 = 0)::Any
return ((p1 + p2) + k1) + k2
end

@test (2 == foo.__code__.co_kwonlyargcount)
@test (Dict("k2" => 0) == foo.__kwdefaults__)
foo.__kwdefaults__ = Dict("k1" => 0)
try
foo(1)
fail(self, "__kwdefaults__ is not properly changed")
catch exn
if exn isa TypeError
#= pass =#
end
end
end

function test_kwonly_methods(self::Example)
mutable struct Example <: AbstractExample

end
function f(self::Example)::Tuple
return (k1, k2)
end

assertEqual(self, f(Example(), 1, 2), (1, 2))
assertEqual(self, f(Example), (1, 2))
assertRaises(self, TypeError, Example.f, 1, 2)
end

function test_issue13343(self::KeywordOnlyArgTestCase)
() -> nothing
end

function test_mangling(self::X)
mutable struct X <: AbstractX

end
function f(self::X)
return __a
end

assertEqual(self, f(X()), 42)
end

function test_default_evaluation_order(self::KeywordOnlyArgTestCase)
a = 42
assertRaises(self, NameError) do err 
function f(v = a, x = b)
#= pass =#
end

end
@test (string(err.exception) == "name \'b\' is not defined")
assertRaises(self, NameError) do err 
f = (v, x) -> nothing
end
@test (string(err.exception) == "name \'b\' is not defined")
end

function main()
keyword_only_arg_test_case = KeywordOnlyArgTestCase()
assertRaisesSyntaxError(keyword_only_arg_test_case)
testSyntaxErrorForFunctionDefinition(keyword_only_arg_test_case)
testSyntaxForManyArguments(keyword_only_arg_test_case)
testTooManyPositionalErrorMessage(keyword_only_arg_test_case)
testSyntaxErrorForFunctionCall(keyword_only_arg_test_case)
testRaiseErrorFuncallWithUnexpectedKeywordArgument(keyword_only_arg_test_case)
testFunctionCall(keyword_only_arg_test_case)
testKwDefaults(keyword_only_arg_test_case)
test_kwonly_methods(keyword_only_arg_test_case)
test_issue13343(keyword_only_arg_test_case)
test_mangling(keyword_only_arg_test_case)
test_default_evaluation_order(keyword_only_arg_test_case)
end

main()