#=
The Computer Language Benchmarks Game
 https://salsa.debian.org/benchmarksgame-team/benchmarksgame/

 direct transliteration of the swift#3 program by Ralph Ganszky and Daniel Muellenborn

 modified for Julia 1.0 by Simon Danisch
 tweaked for performance by maltezfaria and Adam Beckmeyer
=#

using Base.Cartesian

# 0b01111111, 0b10111111, 0b11011111, 0b11101111, etc.
const masks = (0x7f, 0xbf, 0xdf, 0xef, 0xf7, 0xfb, 0xfd, 0xfe)

# Calculate the byte to print for a given vector of 8 real numbers cr
# and a given imaginary component ci. This function should give the
# same result whether prune is true or false but may be faster or
# slower depending on the input.
function mand8(cr, ci, prune)
    r = cr
    t = i = @ntuple 8 _ -> ci

    # In cases where the last call to mand8 resulted in 0x00, the next
    # call is much more likely to result in 0x00, so it's worth it to
    # check several times if the calculation can be aborted
    # early. Otherwise, the relatively costly check can be eliminated.
    if prune
        for _ = 1:10
            for _ = 1:5
                r, i, t = calc_sum(r, i, cr, ci)
            end
            all(>(4.0), t) && return 0x00
        end
    else
        for _ = 1:50
            r, i, t = calc_sum(r, i, cr, ci)
        end
    end

    byte = 0xff # 0b11111111
    for k = 1:8
        t[k] <= 4.0 || (byte &= masks[k])
    end
    byte
end

# Single iteration of mandelbrot calculation for vector r of real
# components and vector i or imaginary components.
@inline function calc_sum(r, i, cr, ci)
    # Using broadcasting (r2 = r .* r) generates operations on llvm
    # <8 x double> vectors even with --cpu-target=core2 (widest simd
    # register on core2 is <2 x double>). @ntuple results in better
    # codegen (uses <2 x double>).
    r2 = @ntuple 8 k -> r[k] * r[k]
    i2 = @ntuple 8 k -> i[k] * i[k]
    ri = @ntuple 8 k -> r[k] * i[k]

    t = @ntuple 8 k -> r2[k] + i2[k]
    r = @ntuple 8 k -> r2[k] - i2[k] + cr[k]
    i = @ntuple 8 k -> ri[k] + ri[k] + ci
    r, i, t
end

# Write n by n portable bitmap image of mandelbrot set to io
function mandelbrot(io, n)
    n % 8 == 0 || error("n must be multiple of 8")

    # Precalculate real coordinates to check
    xvals = Float64[2i / n - 1.5 for i = 0:n-1]
    # Precalculate imaginary coordinates to check
    yvals = Float64[2i / n - 1.0 for i = 0:n-1]

    # Create a vector of bytes to output
    out = Vector{UInt8}(undef, n * n ÷ 8)
    # For each row (each imaginary coordinate), spawn a thread to fill
    # out values. At small values of n, this is too fine-grained of
    # parallelism to really be efficient, but it works well for large n.
    @sync for y = 1:n
        # Threads.@spawn allows dynamic scheduling instead of static scheduling
        # of Threads.@threads macro. See
        # https://github.com/JuliaLang/julia/issues/21017 . On some
        # computers this is faster, on others not.
        Threads.@spawn @inbounds begin
            ci = yvals[y]
            startofrow = (y - 1) * n ÷ 8
            # The first iteration within a row will generally return 0x00
            prune = true
            for x = 1:8:n
                # Calculate whether the (x:x+7)-th real coordinates with
                # the y-th imaginary coordinate belong to the
                # mandelbrot set.
                byte = mand8(@ntuple(8, k -> xvals[x+k-1]), ci, prune)
                out[startofrow+x÷8+1] = byte
                prune = byte == 0x00
            end
        end
    end

    write(io, "P4\n$n $n\n")
    write(io, out)
end

# isinteractive() || mandelbrot(stdout, parse(Int, ARGS[1]))

@time mandelbrot(stdout, 16000)
