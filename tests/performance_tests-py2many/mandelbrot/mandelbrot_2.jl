function mandelbrot(limit, c)::Int64
    z = 0 + 0im
    for i in (0:limit+1-1)
        if abs(z) > 2
            return i
        end
        z = z * z + c
    end
    return i + 1
end

function main()
    mandelbrot(1000000, 0.2 + 0.3im)
end

main()
