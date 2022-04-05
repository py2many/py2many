using Distributed
using ResumableFunctions
using contextlib: closing



@resumable function pixels(y, n, abs)
    range7 = Vector{UInt8}(join((0:6), ""))
    pixel_bits = Vector{UInt8}(join((128 >> pos for pos in (0:7)), ""))
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
    result = Vector{UInt8}(join(split(pixels(y, n, abs))[(n+7)÷8], ""))
    result[end] = result[end] & (255 << (8 - (n % 8)))
    return (y, result)
end

@resumable function ordered_rows(rows, n)
    order = [nothing] * n
    i = 0
    j = n
    while i < length(order)
        if j > 0
            row = next(rows)
            order[row[1]] = row
            j -= 1
        end
        if order[i]
            @yield order[i]
            order[i] = nothing
            i += 1
        end
    end
end

@resumable function compute_rows(n, f)
    row_jobs = ((y, n) for y in (0:n-1))
    if length(Sys.cpu_info()) < 2
        # Unsupported
        @yield_from map(f, row_jobs)
    else

        default_worker_pool() do pool
            unordered_rows = imap_unordered(pool, f, row_jobs)
            # Unsupported
            @yield_from ordered_rows(unordered_rows, n)
        end
    end
end

function mandelbrot(n)
    write_ = x -> write(stdout, x)
    closing(compute_rows(n, compute_row)) do rows
        write_(encode(format("P4\n{0} {0}\n", n)))
        for row in rows
            write_(row[2])
        end
    end
end

function main()
    mandelbrot(parse(Int, argv[2]))
end

main()
