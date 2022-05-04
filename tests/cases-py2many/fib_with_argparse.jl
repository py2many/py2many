abstract type AbstractOptions end

mutable struct Options <: AbstractOptions
    n::Int64
    v::Bool

    Options(n::Int64 = 0, v::Bool = false) = new(n, v)
end

function __repr__(self::AbstractOptions)::String
    return AbstractOptions(self.n, self.v)
end


function __eq__(self::AbstractOptions, other::AbstractOptions)::Bool
    return __key(self) == __key(other)
end


function __key(self::AbstractOptions)
    (self.n, self.v)
end

function fib(i::Int64)::Int64
    if i == 0 || i == 1
        return 1
    end
    return fib(i - 1) + fib(i - 2)
end

function main()
    args = parse_args(Options)
    if n(args) == 0
        n(args) = 5
    end
    println(fib(n(args)))
end

main()
