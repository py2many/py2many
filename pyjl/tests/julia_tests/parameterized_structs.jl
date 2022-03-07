using Parameters

@macroexpand @with_kw struct PhysicalPara{R}
    rw::R = 1000.
    ri::R = 900.
    L::R = 3.34e5
    g::R = 9.81
    cw::R = 4220.
    day::R = 24*3600.
end

# Parameter independence
@with_kw struct Para2{R<:Real} @deftype R
    a = 5
    b
    c = a+b
    d::Int = 4 # adding a type overrides the @deftype
end

pa2 = Para2(b=7)
# Defines new struct as follows:
# Para2{Int64}
#   a: Int64 5
#   b: Int64 7
#   c: Int64 12 # Notice how c gets updated
#   d: Int64 4

# Struct with default constructors. One includes kwargs with default values
# For more information, see: https://docs.julialang.org/en/v1/manual/constructors/
struct PhyPara
    rw::Float64
    ri::Float64
    L::Float64
    g::Float64
    cw::Float64
    day::Float64
    PhyPara(;rw=1000., ri=900., L=3.34e5, g=9.81, cw=4220., day=24*3600.) = 
        new(rw, ri, L, g, cw, day)
    PhyPara(rw, ri, L, g, cw, day) = 
        new(rw, ri, L, g, cw, day)
end