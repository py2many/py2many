
function sieve(n)::Int64
    primes = repeat([true], (n + 1))
    counter = 0
    for i = 2:n-1
        if primes[i+1]
            counter = counter + 1
            for j = i*i:i:n-1
                primes[j+1] = false
            end
        end
    end
    return counter
end

if abspath(PROGRAM_FILE) == @__FILE__
    sieve(parse(Int, append!([PROGRAM_FILE], ARGS)[2]))
end
