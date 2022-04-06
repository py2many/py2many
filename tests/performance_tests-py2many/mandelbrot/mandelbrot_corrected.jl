using Distributed
using ResumableFunctions



@resumable function pixels(y, n, abs)
    range7 = Vector{UInt8}((0:6))
    pixel_bits = Vector{UInt8}((128 >> pos for pos in (0:7)))
    c1 = 2.0 / float(n)
    c0 = (-1.5 + 1im * y * c1) - 1im
    x = 0
    while true
        pixel = 0
        c = x * c1 + c0
        for pixel_bit in pixel_bits
            z = c
            for _ in range7
                for _ in range7
                    z = z * z + c
                end
                if abs(z) >= 2.0
                    break
                end
            end
            c += c1
        end
        @yield pixel
        x += 8
    end
end

function compute_row(p)::Tuple
    y, n = p
    pixels_p = pixels(y, n, abs)
    result = Vector{UInt8}()
    for v in (0:(n+7)÷8)
        push!(result, pixels_p())
    end
    result[end] = result[end] & (255 << (8 - (n % 8)))
    return (y, result)
end

@resumable function compute_rows(n, f)
    row_jobs = ((y, n) for y = 0:n-1)
    for v in map(f, row_jobs)
        @yield v
    end
end

function mandelbrot(n)
    write_ = x -> write(stdout, x)
    write_("P4\n$n $n\n")
    for row in compute_rows(n, compute_row)
        write_(row[2])
    end
end

function main()
    @time mandelbrot(2000)
    # mandelbrot(parse(Int, argv[2]))
end

main()
