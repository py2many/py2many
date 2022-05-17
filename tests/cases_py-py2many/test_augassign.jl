using Test

abstract type AbstractAugAssignTest end
abstract type Abstractaug_test end
abstract type Abstractaug_test2 <: Abstractaug_test end
abstract type Abstractaug_test3 <: Abstractaug_test end
abstract type Abstractaug_test4 <: Abstractaug_test3 end
abstract type Abstracttestall end
output = []
mutable struct aug_test <: Abstractaug_test
val
end
function __radd__(self::aug_test, val)::Any
return self.val + val
end

function __add__(self::aug_test, val)::aug_test
return aug_test(self.val + val)
end

mutable struct aug_test2 <: Abstractaug_test2
val
end
function __iadd__(self::aug_test2, val)
self.val = self.val + val
return self
end

mutable struct aug_test3 <: Abstractaug_test3
val
end
function __iadd__(self::aug_test3, val)::aug_test3
return aug_test3(self.val + val)
end

mutable struct aug_test4 <: Abstractaug_test4
#= Blocks inheritance, and fallback to __add__ =#
__iadd__

                    aug_test4(__iadd__ = nothing) =
                        new(__iadd__)
end

mutable struct testall <: Abstracttestall

end
function __add__(self::testall, val)
push!(output, "__add__ called")
end

function __radd__(self::testall, val)
push!(output, "__radd__ called")
end

function __iadd__(self::testall, val)
push!(output, "__iadd__ called")
return self
end

function __sub__(self::testall, val)
push!(output, "__sub__ called")
end

function __rsub__(self::testall, val)
push!(output, "__rsub__ called")
end

function __isub__(self::testall, val)
push!(output, "__isub__ called")
return self
end

function __mul__(self::testall, val)
push!(output, "__mul__ called")
end

function __rmul__(self::testall, val)
push!(output, "__rmul__ called")
end

function __imul__(self::testall, val)
push!(output, "__imul__ called")
return self
end

function __matmul__(self::testall, val)
push!(output, "__matmul__ called")
end

function __rmatmul__(self::testall, val)
push!(output, "__rmatmul__ called")
end

function __imatmul__(self::testall, val)
push!(output, "__imatmul__ called")
return self
end

function __floordiv__(self::testall, val)
push!(output, "__floordiv__ called")
return self
end

function __ifloordiv__(self::testall, val)
push!(output, "__ifloordiv__ called")
return self
end

function __rfloordiv__(self::testall, val)
push!(output, "__rfloordiv__ called")
return self
end

function __truediv__(self::testall, val)
push!(output, "__truediv__ called")
return self
end

function __rtruediv__(self::testall, val)
push!(output, "__rtruediv__ called")
return self
end

function __itruediv__(self::testall, val)
push!(output, "__itruediv__ called")
return self
end

function __mod__(self::testall, val)
push!(output, "__mod__ called")
end

function __rmod__(self::testall, val)
push!(output, "__rmod__ called")
end

function __imod__(self::testall, val)
push!(output, "__imod__ called")
return self
end

function __pow__(self::testall, val)
push!(output, "__pow__ called")
end

function __rpow__(self::testall, val)
push!(output, "__rpow__ called")
end

function __ipow__(self::testall, val)
push!(output, "__ipow__ called")
return self
end

function __or__(self::testall, val)
push!(output, "__or__ called")
end

function __ror__(self::testall, val)
push!(output, "__ror__ called")
end

function __ior__(self::testall, val)
push!(output, "__ior__ called")
return self
end

function __and__(self::testall, val)
push!(output, "__and__ called")
end

function __rand__(self::testall, val)
push!(output, "__rand__ called")
end

function __iand__(self::testall, val)
push!(output, "__iand__ called")
return self
end

function __xor__(self::testall, val)
push!(output, "__xor__ called")
end

function __rxor__(self::testall, val)
push!(output, "__rxor__ called")
end

function __ixor__(self::testall, val)
push!(output, "__ixor__ called")
return self
end

function __rshift__(self::testall, val)
push!(output, "__rshift__ called")
end

function __rrshift__(self::testall, val)
push!(output, "__rrshift__ called")
end

function __irshift__(self::testall, val)
push!(output, "__irshift__ called")
return self
end

function __lshift__(self::testall, val)
push!(output, "__lshift__ called")
end

function __rlshift__(self::testall, val)
push!(output, "__rlshift__ called")
end

function __ilshift__(self::testall, val)
push!(output, "__ilshift__ called")
return self
end

mutable struct AugAssignTest <: AbstractAugAssignTest

end
function testBasic(self::AugAssignTest)
x = 2
x += 1
x *= 2
x ^= 2
x -= 8
x ÷= 5
x %= 3
x = x & 2
x |= 5
x = x  ⊻  1
x /= 2
@test (x == 3.0)
end

function testInList(self::AugAssignTest)
x = [2]
x[1] += 1
x[1] *= 2
x[1] ^= 2
x[1] -= 8
x[1] ÷= 5
x[1] %= 3
x[1] = x[1] & 2
x[1] |= 5
x[1] = x[1]  ⊻  1
x[1] /= 2
@test (x[1] == 3.0)
end

function testInDict(self::AugAssignTest)
x = Dict(0 => 2)
x[0] += 1
x[0] *= 2
x[0] ^= 2
x[0] -= 8
x[0] ÷= 5
x[0] %= 3
x[0] = x[0] & 2
x[0] |= 5
x[0] = x[0]  ⊻  1
x[0] /= 2
@test (x[0] == 3.0)
end

function testSequences(self::AugAssignTest)
x = [1, 2]
z = x
x = append!(x, [3, 4])
@test x == z
x = repeat(x,2)
@test (x == [1, 2, 3, 4, 1, 2, 3, 4])
x = [1, 2, 3]
y = x
splice!(x, 2:2, repeat(x[2:2],2))
splice!(y, 3:2, [1])
@test (x == [1, 2, 1, 2, 3])
@test x == y
end

function testCustomMethods1(self::AugAssignTest)
x = aug_test(1)
y = x
x = __add__(x, 10)
@test y != x
@test (x.val == 11)
x = aug_test2(2)
y = x
x = __add__(x, 10)
@test (x.val == 12)
x = aug_test3(3)
y = x
x = __add__(x, 10)
@test isa(self, x)
@test y != x
@test (x.val == 13)
x = aug_test4(4)
assertRaises(self, TypeError) do 
x = __add__(x, 10)
end
end

function testCustomMethods2(test_self)
x = testall()
__add__(x, 1)
__add__(1, x)
x = __add__(x, 1)
__sub__(x, 1)
__sub__(1, x)
x = __sub__(x, 1)
__mul__(x, 1)
__mul__(1, x)
x = __mul__(x, 1)
__matmul__(x, 1)
__matmul__(1, x)
x = __matmul__(x, 1)
__div__(x, 1)
__div__(1, x)
x = __div__(x, 1)
__floordiv__(x, 1)
__floordiv__(1, x)
x = __floordiv__(x, 1)
__mod__(x, 1)
__mod__(1, x)
x = __mod__(x, 1)
__pow__(x, 1)
__pow__(1, x)
x = __pow__(x, 1)
__or__(x, 1)
__or__(1, x)
x = __or__(x, 1)
__and__(x, 1)
__and__(1, x)
x = __and__(x, 1)
__xor__(x, 1)
__xor__(1, x)
x = __xor__(x, 1)
__rshift__(x, 1)
__rshift__(1, x)
x = __rshift__(x, 1)
__lshift__(x, 1)
__lshift__(1, x)
x = __lshift__(x, 1)
@test (output == splitlines("__add__ called\n__radd__ called\n__iadd__ called\n__sub__ called\n__rsub__ called\n__isub__ called\n__mul__ called\n__rmul__ called\n__imul__ called\n__matmul__ called\n__rmatmul__ called\n__imatmul__ called\n__truediv__ called\n__rtruediv__ called\n__itruediv__ called\n__floordiv__ called\n__rfloordiv__ called\n__ifloordiv__ called\n__mod__ called\n__rmod__ called\n__imod__ called\n__pow__ called\n__rpow__ called\n__ipow__ called\n__or__ called\n__ror__ called\n__ior__ called\n__and__ called\n__rand__ called\n__iand__ called\n__xor__ called\n__rxor__ called\n__ixor__ called\n__rshift__ called\n__rrshift__ called\n__irshift__ called\n__lshift__ called\n__rlshift__ called\n__ilshift__ called\n"))
end

function main()
aug_assign_test = AugAssignTest()
testBasic(aug_assign_test)
testInList(aug_assign_test)
testInDict(aug_assign_test)
testSequences(aug_assign_test)
testCustomMethods1(aug_assign_test)
testCustomMethods2(aug_assign_test)
end

main()