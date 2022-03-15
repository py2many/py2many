using argparse_dataclass: dataclass
abstract type AbstractOptions end
mutable struct Options <: AbstractOptions

end

                function __init__(self::AbstractOptions, )
                    setfield!(self::AbstractOptions, :, )
                end
            

                function __repr__(self::AbstractOptions)::String 
                    return AbstractOptions(self.) 
                end
            

                function __eq__(self::AbstractOptions, other::AbstractOptions)::Bool
                    return __key(self) == __key(other)
                end
            

                function __key(self::AbstractOptions)
                    (self.)
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
