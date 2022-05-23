abstract type AbstractHello end
mutable struct Hello <: AbstractHello
end
function test(self::Hello)::String
    return "ola"
end

if abspath(PROGRAM_FILE) == @__FILE__
    a = "a"
    b = "ab"
    @assert(join(b, a) == "aab")
    tuple = ("One", "Two", "Three")
    value_str = join(tuple, " ")
    @assert(value_str == "One Two Three")
    tuple_2 = ["The", "challenge", "is", "on"]
    value_str_2 = join(["The", "challenge", "is", "on"], "#")
    @assert(value_str_2 == "The#challenge#is#on")
    @assert(join([test(Hello()), "adeus"], " ") == "ola adeus")
    @assert(join([test(Hello()), "adeus"], "\n") == "ola\nadeus")
    println("OK")
end
