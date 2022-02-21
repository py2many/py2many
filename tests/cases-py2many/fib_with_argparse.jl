using argparse_dataclass: dataclass
abstract type AbstractOptions end
mutable struct Options <: AbstractOptions
    v::Bool
    n::Int64
end

function __init__(self::Options, v::Bool, n::Int64)
    setfield!(self::Options, :v, v::Bool)
    setfield!(self::Options, :n, n::Int64)

end

function __repr__(self::Options)::String
    return Options(getfield!(self::Options, v::Bool), getfield!(self::Options, n::Int64))
end
function __eq__(self::Options, other::Options)::Bool
    return __key(self) == __key(other)
end

function __key(self::Options)
    (getfield!(self::Options, v::Bool), getfield!(self::Options, n::Int64))
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
