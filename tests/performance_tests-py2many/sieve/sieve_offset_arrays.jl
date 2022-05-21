using OffsetArrays

function sieve(n)::Int64
    primes = OffsetArray(repeat([true], (n + 1)), -1)
    counter = 0
    for i = 2:n-1
        if primes[i]
            counter = counter + 1
            for j = i*i:i:n
                primes[j] = false
            end
        end
    end
    return counter
end

if abspath(PROGRAM_FILE) == @__FILE__
    @assert(sieve(10000000) == 664579)
end
