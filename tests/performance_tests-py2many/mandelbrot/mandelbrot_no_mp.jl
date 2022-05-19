using ResumableFunctions
using StringEncodings

@resumable function pixels(y, n, abs)
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
            has_break = false
            for _ in range7
                for _ in range7
                    z = z * z + c
                end
                if abs(z) >= 2.0
                    has_break = true
                    break
                end
            end
            if has_break != true
                pixel += pixel_bit
            end
            c += c1
        end
        @yield pixel
        x += 8
    end
end

function compute_row(p)
    y, n = p
    pixels_ = pixels(y, n, abs)
    result = Vector{UInt8}([pixels_() for _ in (0:(n+7)÷8)])
    result[end] = result[end] & 255 << (8 - (n % 8))
    return (y, result)
end

@resumable function compute_rows(n, f)
    row_jobs = ((y, n) for y = 0:n-1)
    for v in map(f, row_jobs)
        @yield v
    end
end

function mandelbrot(n)
    write = x -> Base.write(stdout, x)
    write(encode("P4\n$(n) $(n)\n", "UTF-8"))
    for row in compute_rows(n, compute_row)
        write(row[2])
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    mandelbrot(20)
end
