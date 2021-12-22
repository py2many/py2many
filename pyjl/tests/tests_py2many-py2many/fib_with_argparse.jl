using DataClass
using argparse_dataclass: dataclass
@dataclass mutable struct Options
v::Bool
n::Int64
_initvars = [_init=true, _repr=true, _eq=true, _order=false, _unsafe_hash=false, _frozen=false]
end

function fib(i::Int64)::Int64
if i == 0 || i == 1
return 1
end
return (fib((i - 1)) + fib((i - 2)))
end

function main()
args = ::from_args()
if args.n == 0
args.n = 5
end
println(fib(args.n));
end

main()
