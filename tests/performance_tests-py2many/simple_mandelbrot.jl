MAX_ITER = 10000000
function mandelbrot(c)::Int64
    z = 0
    n = 0
    while abs(z) <= 2 && n < MAX_ITER
        z = z * z + c
        n += 1
    end
    return n
end

function main()
    map = []
    for a in (-10:5:9)
        for b in (-10:5:9)
            c = complex(a / 10, b / 10)
            push!(map, (c, mandelbrot(c)))
        end
    end
end

main()
