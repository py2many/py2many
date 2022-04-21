function mandelbrot(limit, c)::Int64
    z = 0 + 0im
    i = nothing
    for _i = 0:limit+1-1
        i = _i
        if abs(z) > 2
            return i
        end
        z = z * z + c
    end
    return i + 1
end

function main()
    @assert(mandelbrot(1000000, 0.2 + 0.3im) == 1000001)
end

main()
