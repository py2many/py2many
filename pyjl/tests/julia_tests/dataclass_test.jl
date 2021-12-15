using Pkg; Pkg.add(url="https://github.com/MiguelMarcelino/Dataclass.jl")

# Adding Path of module to LOAD_PATH (is this needed?)
# push!(Base.load_path(), "C:\\Users\\Miguel Marcelino\\.julia\\packages\\Dataclass\\x82Dn\\src") # don't use
# push!(LOAD_PATH, "C:\\Users\\Miguel Marcelino\\.julia\\packages\\Dataclass\\x82Dn\\src")

# Start using DataClass
using DataClass

# The following fails (Dataclass with small 'c' outputs error)
# using Dataclass

@dataclass mutable struct Test
    valueInt::Int64
    valueStr::String
    _initvars = [_init=true, _repr=true, _eq=true, _order=true, _unsafe_hash=false, _frozen=true]
end

function func()
    test = Test(1, "new")
    __init__(test, 8, "test")
    print(test)
end

func()