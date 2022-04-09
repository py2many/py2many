using Test
abstract type AbstractAugAssignTest end

mutable struct AugAssignTest <: AbstractAugAssignTest

end
function testBasic(self::AbstractAugAssignTest)
    x = 2
    x += 1
    x *= 2
    x ^= 2
    x -= 8
    x ÷= 5
    x %= 3
    x = x & 2
    x |= 5
    x = x ⊻ 1
    x /= 2
    @test (x == 3.0)
end

function testInList(self::AbstractAugAssignTest)
    x = [2]
    x[1] = x[1] + 1
    x[1] = x[1] * 2
    x[1] ^= 2
    x[1] -= 8
    x[1] ÷= 5
    x[1] %= 3
    x[1] = x[1] & 2
    x[1] |= 5
    x[1] = x[1] ⊻ 1
    x[1] /= 2
    @test (x[1] == 3.0)
end

function testInDict(self::AbstractAugAssignTest)
    x = Dict(0 => 2)
    x[0] += 1
    x[0] *= 2
    x[0] ^= 2
    x[0] -= 8
    x[0] ÷= 5
    x[0] %= 3
    x[0] = x[0] & 2
    x[0] |= 5
    x[0] = x[0] ⊻ 1
    x[0] /= 2
    @test (x[0] == 3.0)
end

function testSequences(self::AbstractAugAssignTest)
    x = [1, 2]
    z = x
    x = append!(x, [3, 4])
    @test x == z
    x = repeat(x, 2)
    @test (x == [1, 2, 3, 4, 1, 2, 3, 4])
    x = [1, 2, 3]
    y = x
    splice!(x, 2:2, repeat(x[2:2], 2))
    splice!(y, 3:2, [1])
    @test (x == [1, 2, 1, 2, 3])
    @test x == y
end

function main()
    aug_assign_test = AugAssignTest()
    testBasic(aug_assign_test)
    testInList(aug_assign_test)
    testInDict(aug_assign_test)
    testSequences(aug_assign_test)
end

main()
