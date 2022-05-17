using Test

abstract type AbstractLongExpText end
mutable struct LongExpText <: AbstractLongExpText

end
function test_longexp(self::LongExpText)
REPS = 65580
l = eval("[" * repeat("2,",REPS) * "]")
@test (length(l) == REPS)
end

function main()
long_exp_text = LongExpText()
test_longexp(long_exp_text)
end

main()