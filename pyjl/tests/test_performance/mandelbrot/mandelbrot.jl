using contextlib: closing
using itertools: islice


function pixels(y, n, abs)
channel_pixels = Channel(1)
range7 = Vector{Int8}((0:6))
pixel_bits = Vector{Int8}((128 >> pos for pos in (0:7)))
c1 = 2.0 / float(n)
c0 = (-1.5 + 1im*y*c1) - 1im
x = 0
while true
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
put!(channel_pixels, pixel);
x += 8
end
close((channel_pixels))
return channel_pixels
end

function compute_row(p)
y, n = p
result = Vector{Int8}(split(pixels(y, n, abs))[(n + 7) / 8])
result[end] &= 255 << (8 - (n % 8))
return (y, result)
end

function ordered_rows(rows, n)
channel_ordered_rows = Channel(1)
order = [nothing]*n
i = 0
j = n
while i < length(order)
if j > 0
row = next(rows)
order[row[1]] = row
j -= 1
end
if order[i]
put!(channel_ordered_rows, order[i]);
order[i] = nothing
i += 1
end
end
close((channel_ordered_rows))
return channel_ordered_rows
end

function compute_rows(n, f)
channel_compute_rows = Channel(1)
row_jobs = ((y, n) for y in (0:n - 1))
if length(Sys.cpu_info()) < 2
for value_compute_rows in map(f, row_jobs)
put!(channel_compute_rows, value_compute_rows)
end;
else
for value_compute_rows in ordered_rows(map(f, row_jobs), n)
put!(channel_compute_rows, value_compute_rows)
end;
end
close((channel_compute_rows))
return channel_compute_rows
end

function mandelbrot(n)
rows = compute_rows(n, compute_row)
println(encode("P4\n{0} {0}\n".format(n)));
for row in rows
println(row[2]);
end
end

function main()
num::Int64 = 16000
mandelbrot(1000);
end

main()
