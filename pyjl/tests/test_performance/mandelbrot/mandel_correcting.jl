# using contextlib: closing
# using itertools: islice


function pixels(y, n, abs)
c_pixels = Channel(1)
range7 = Vector{UInt8}(join((0:6), ""))
pixel_bits = Vector{UInt8}(join((128 >> pos for pos in (0:7)), ""))
c1 = 2.0 / float(n)
c0 = (-1.5 + 1im*y*c1) - 1im
x = 0
t_pixels = @async while true
pixel = 0
c = x*c1 + c0
for pixel_bit in pixel_bits
z = c
for _ in range7
for _ in range7
z = z*z + c
end
if abs(z) >= 2.0
break;
end
end
c += c1
end
put!(c_pixels, pixel);
x += 8
end
bind(c_pixels, t_pixels)
end

function compute_row(p)
y, n = p
result = Vector{UInt8}(join(split(pixels(y, n, abs))[(n + 7) / 8], ""))
result[end] &= 255 << (8 - (n % 8))
return (y, result)
end

function ordered_rows(rows, n)
c_ordered_rows = Channel(1)
order = [nothing]*n
i = 0
j = n
t_ordered_rows = @async while i < length(order)
if j > 0
row = next(rows)
order[row[1]] = row
j -= 1
end
if order[i]
put!(c_ordered_rows, order[i]);
order[i] = nothing
i += 1
end
end
bind(c_ordered_rows, t_ordered_rows)
end

function compute_rows(n, f)
c_compute_rows = Channel(1)
row_jobs = ((y, n) for y in (0:n - 1))
if length(Sys.cpu_info()) < 2
t_compute_rows = @async for v_compute_rows in map(f, row_jobs)
put!(c_compute_rows, v_compute_rows)
end;
else
t_compute_rows = @async for v_compute_rows in ordered_rows(map(f, row_jobs), n)
put!(c_compute_rows, v_compute_rows)
end;
end
bind(c_compute_rows, t_compute_rows)
end

function mandelbrot(n)
rows = compute_rows(n, compute_row)
println("P4\n" * string(n) * " " * string(n) * "\n");
for row in rows
println(row[2]);
end
end

function main()
num::Int64 = 16000
mandelbrot(1000);
end

main()
