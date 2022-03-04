using argparse_dataclass: dataclass
abstract type AbstractOptions end

mutable struct Options <: AbstractOptions
    v::Bool
    n::Int64
end
function Options(v::Any = false, n::Any = 0)::Options
    return Options(v, n)
end


function __init__(self::AbstractOptions, v::Bool, n::Int64)
    setfield!(self::AbstractOptions, :v, v::Bool),
    setfield!(self::AbstractOptions, :n, n::Int64)
end


function __repr__(self::AbstractOptions)::String
    return AbstractOptions(self.v, self.n)
end


function __eq__(self::AbstractOptions, other::AbstractOptions)::Bool
    return __key(self) == __key(other)
end


function __key(self::AbstractOptions)
    (self.v, self.n)
end


function fib(i::Int64)::Int64
    if i == 0 || i == 1
        return 1
    end
    return fib(i - 1) + fib(i - 2)
end

function main()
    args = parse_args(Options)
    if args.n == 0
        args.n = 5
    end
    println(fib(args.n))
end

main()
