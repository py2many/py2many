PI = 3.141592653589793
SOLAR_MASS = 4 * PI * PI
DAYS_PER_YEAR = 365.24
BODIES = Dict(
    "sun" => ([0.0, 0.0, 0.0], [0.0, 0.0, 0.0], SOLAR_MASS), 
    "jupiter" => (
        [4.841431442464721, 
         -1.1603200440274284, 
         -0.10362204447112311], 
        [0.001660076642744037 * DAYS_PER_YEAR, 
         0.007699011184197404 * DAYS_PER_YEAR, 
          -6.90460016972063e-05 * DAYS_PER_YEAR], 
        0.0009547919384243266 * SOLAR_MASS), 
    "saturn" => (
        [8.34336671824458, 
         4.124798564124305, 
         -0.4035234171143214], 
        [-0.002767425107268624 * DAYS_PER_YEAR, 
         0.004998528012349172 * DAYS_PER_YEAR, 
         2.3041729757376393e-05 * DAYS_PER_YEAR], 
        0.0002858859806661308 * SOLAR_MASS), 
    "uranus" => (
        [12.894369562139131, 
         -15.111151401698631, 
         -0.22330757889265573], 
        [0.002964601375647616 * DAYS_PER_YEAR, 
         0.0023784717395948095 * DAYS_PER_YEAR, 
         -2.9658956854023756e-05 * DAYS_PER_YEAR], 
        4.366244043351563e-05 * SOLAR_MASS), 
    "neptune" => (
        [15.379697114850917, 
         -25.919314609987964, 
         0.17925877295037118], 
        [0.0026806777249038932 * DAYS_PER_YEAR, 
         0.001628241700382423 * DAYS_PER_YEAR, 
         -9.515922545197159e-05 * DAYS_PER_YEAR], 
        5.1513890204661145e-05 * SOLAR_MASS)
    )
SYSTEM = collect(values(BODIES))

function combinations(l)::Vector
    result = []
    # result::Vector{Tuple{Tuple{Vector{Float64}, 
    #         Vector{Float64}, Float64},
    #     Tuple{Vector{Float64},
    #         Vector{Float64}, Float64}}} = []
    for x in (0:length(l)-1-1)
        ls = l[(x+1+1):end]
        for y in ls
            push!(result, (l[x+1], y))
        end
    end
    return result
    # return [e for e in result]
    # return typeof(result[1])[result...]
    # return convert(Vector{typeof(result[1])}, result)
end

# @code_lowered combinations(SYSTEM)
@code_typed combinations(SYSTEM)
