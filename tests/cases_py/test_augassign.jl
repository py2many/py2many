using Test
abstract type AbstractAugAssignTest end

mutable struct AugAssignTest <: AbstractAugAssignTest

end
function testSequences(self::AbstractAugAssignTest)
    x = [1, 2, 3]
    y = x
    x[2:2] = x[2:2] * 2
    y[2:2] = y[2:2] + [1]
    @test (x == [1, 2, 1, 2, 3])
    @test x == y
end

function main()
    aug_assign_test = AugAssignTest()
    testSequences(aug_assign_test)
end

main()
