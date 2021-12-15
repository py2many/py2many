# include("../../addons/PyEnum/PyEnum.jl")
using Pkg; Pkg.add(url="https://github.com/MiguelMarcelino/PyEnum")
# using PyEnum

@pyenum(Test, Ola=1, Adeus=2)