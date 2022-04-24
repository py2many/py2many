




function pixels(y::Any, n::Any, abs::Any)
    Channel() do ch_pixels
        range7 = Vector{UInt8}(0:6)
        pixel_bits = Vector{UInt8}([128 >> pos for pos = 0:7])
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
            put!(ch_pixels, pixel)
            x += 8
        end
    end
end

function compute_row(p::Any)::Tuple
    y, n = p
    result = Vector{UInt8}([pixels(y, n, abs) for _ in (0:(n+7)÷8)])
    result[end+1] = result[end+1] & 255 << (8 - (n % 8))
    return (y, result)
end

function compute_rows(n::Any, f::Any)
    row_jobs = ((y, n) for y = 0:n-1)
    # Unsupported
    @yield_from map(f, row_jobs)
end

function mandelbrot(n::Any)
    write = x -> Base.write(stdout, x)
    compute_rows(n, compute_row) do rows
        write(Vector{UInt8}("P4\n$n $n\n"))
        for row in rows
            write(row[2])
        end
    end
end

function main()
    mandelbrot(2000)
end

main()
