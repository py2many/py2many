using Distributed
using StringEncodings

function pixels(y, n, abs)
    Channel() do ch_pixels
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
                put!(ch_pixels, pixel)
                x += 8
            end
        end
    end
end

function compute_row(p)
    y, n = p
    result = Vector{UInt8}([pixels(y, n, abs) for _ in (0:(n+7)÷8)])
    result[end] = result[end] & 255 << (8 - (n % 8))
    return (y, result)
end

function ordered_rows(rows, n)
    Channel() do ch_ordered_rows
        Channel() do ch_ordered_rows
            order = [nothing] * n
            i = 0
            j = n
            while i < length(order)
                if j > 0
                    row = next(rows)
                    order[row[1]+1] = row
                    j -= 1
                end
                if order[i+1]
                    put!(ch_ordered_rows, order[i+1])
                    order[i+1] = nothing
                    i += 1
                end
            end
        end
    end
end

function compute_rows(n, f)
    Channel() do ch_compute_rows
        Channel() do ch_compute_rows
            row_jobs = ((y, n) for y = 0:n-1)
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
    end
end

function mandelbrot(n)
    write = x -> Base.write(stdout, x)
    compute_rows(n, compute_row) do rows
        write(encode("P4\n$(n) $(n)\n", "UTF-8"))
        for row in rows
            write(row[2])
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    mandelbrot(20)
end
