function mandelbrot(limit, c)::Int64
    z = 0 + 0im
    for i = 0:limit
        if abs(z) > 2
            return i
        end
        z = z * z + c
    end
    return i + 1
end

if abspath(PROGRAM_FILE) == @__FILE__
    @assert(mandelbrot(1, 0.2 + 0.3im) == 2)
    @assert(mandelbrot(5, 0.2 + 0.3im) == 6)
    @assert(mandelbrot(6, 0.2 + 0.3im) == 7)
    @assert(mandelbrot(10000, 1 + 0.3im) == 2)
    @assert(mandelbrot(10000, 0.6 + 0.4im) == 4)
end
